import math
import re
import os
import time
import chardet
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from collections import defaultdict
import threading

class ArcSubdivider:
    def __init__(self, angular_resolution=1.0, log_message=None):
        self.angular_resolution = angular_resolution
        # 独立跟踪每个轴的位置
        self.axis_pos = defaultdict(float)
        # 独立跟踪每个轴最后更新的位置
        self.last_axis_update = defaultdict(float)
        self.arc_plane = 'G17'
        self.distance_mode = 'G90'
        self.feed_rate = None
        self.output_lines = []
        self.log_message = log_message or (lambda msg: None)
        self.last_motion_command = None
        self.current_line_number = None  # 当前处理的行号
        
    def parse_gcode_line(self, line):
        """解析G代码行 - 改进版本，正确处理带行号的指令和模态命令"""
        # 移除注释
        clean_line = re.sub(r'\(.*?\)', '', line).strip()
        if not clean_line:
            return None, None, {}  # 返回 (行号, 命令, 参数)
        
        # 初始化行号和指令部分
        line_number = None
        command_part = clean_line
        
        # 处理带行号的指令
        if clean_line.startswith('N') and re.match(r'^N\d+', clean_line):
            # 分离行号和指令
            parts = re.split(r'\s+', clean_line, 1)
            line_number = parts[0].strip()
            if len(parts) > 1:
                command_part = parts[1].strip()
            else:
                command_part = ""
        
        # 分割指令 - 改进处理模态命令
        parts = re.findall(r'([A-Z][0-9\.\+\-]*)', command_part)
        if not parts:
            return line_number, None, {}
        
        # 检查是否是G/M命令还是轴参数
        command = None
        params = {}
        for part in parts:
            if part[0].isalpha() and len(part) > 1:
                axis = part[0]
                # 如果是G或M命令
                if axis in ['G', 'M']:
                    command = part
                else:  # 轴参数
                    try:
                        value_str = part[1:]
                        if value_str.endswith('.'):
                            value_str += '0'
                        value = float(value_str)
                        params[axis] = value
                    except ValueError:
                        self.log_message(f"无法解析参数: {part}")
        return line_number, command, params
    
    def update_axis_position(self, params):
        """更新各轴位置 - 独立更新每个轴"""
        changes = []
        for axis, value in params.items():
            if axis in ['X', 'Y', 'Z']:  # 只处理坐标轴
                # 记录该轴最后更新的位置
                old_value = self.last_axis_update[axis]
                
                if self.distance_mode == 'G90':  # 绝对坐标
                    self.axis_pos[axis] = value
                    self.last_axis_update[axis] = value
                    if abs(old_value - value) > 0.001:
                        changes.append(f"{axis}: {old_value:.4f} → {value:.4f}")
                else:  # 增量坐标
                    new_value = self.axis_pos[axis] + value
                    self.axis_pos[axis] = new_value
                    self.last_axis_update[axis] = new_value
                    changes.append(f"{axis}: +{value:.4f} → {new_value:.4f}")
        
        if changes:
            self.log_message("位置更新: " + ", ".join(changes))
    
    def get_arc_start_point(self):
        """获取圆弧起点位置 - 使用每个轴最后独立更新的值"""
        start_point = {
            'X': self.last_axis_update['X'],
            'Y': self.last_axis_update['Y'],
            'Z': self.last_axis_update['Z']
        }
        return start_point
    
    def calculate_arc_center_ij(self, end_x, end_y, i_offset, j_offset, arc_command):
        """计算I/J格式圆弧圆心"""
        # 获取起点
        start_point = self.get_arc_start_point()
        start_x = start_point['X']
        start_y = start_point['Y']
        
        # I/J是相对于起点的偏移量
        center_x = start_x + i_offset
        center_y = start_y + j_offset
        
        # 计算半径
        radius = math.sqrt(i_offset**2 + j_offset**2)
        
        self.log_message(f"I/J圆弧: 起点({start_x:.4f}, {start_y:.4f}), 终点({end_x:.4f}, {end_y:.4f}), I={i_offset:.4f}, J={j_offset:.4f}")
        self.log_message(f"圆心: ({center_x:.4f}, {center_y:.4f}), 半径={radius:.4f}")
        
        # 验证终点到圆心的距离
        end_radius = math.sqrt((end_x - center_x)**2 + (end_y - center_y)**2)
        radius_diff = abs(end_radius - radius)
        
        if radius_diff > 0.01:  # 允许10微米误差
            self.log_message(f"警告: 终点半径={end_radius:.4f}与起点半径={radius:.4f}不匹配，误差={radius_diff:.6f}")
        
        return center_x, center_y, radius
    
    def calculate_arc_center(self, end_x, end_y, radius, arc_command):
        """计算圆弧圆心 - 修复圆心方向错误问题"""
        # 获取当前所有轴的最近位置作为起点
        start_point = self.get_arc_start_point()
        start_x = start_point['X']
        start_y = start_point['Y']
        
        self.log_message(f"R格式圆弧: 起点({start_x:.4f}, {start_y:.4f}), 终点({end_x:.4f}, {end_y:.4f}), R={radius:.4f}, {arc_command}")
        
        # 检查起点终点是否重合
        if abs(start_x - end_x) < 0.001 and abs(start_y - end_y) < 0.001:
            self.log_message("警告: 圆弧起点和终点重合，无法计算圆心")
            return None
        
        # 计算弦长
        dx = end_x - start_x
        dy = end_y - start_y
        chord_length = math.sqrt(dx**2 + dy**2)
        
        # 检查半径有效性
        if chord_length > 2 * abs(radius):
            self.log_message(f"几何错误: 弦长={chord_length:.4f} > 直径={2*abs(radius):.4f}")
            return None
        
        # 计算弦的中点
        mid_x = (start_x + end_x) / 2
        mid_y = (start_y + end_y) / 2
        
        # 计算弦的垂直距离
        actual_radius = abs(radius)
        height = math.sqrt(actual_radius**2 - (chord_length/2)**2)
        
        # 计算垂直于弦的单位向量
        # 弦的方向向量: (dx, dy)
        # 垂直向量(右手): (dy, -dx) 或 (-dy, dx)
        perp_length = chord_length
        
        # 根据G2/G3和半径符号确定圆心位置
        # G2顺时针: 圆心在弦的右侧(刀具视角)
        # G3逆时针: 圆心在弦的左侧(刀具视角)
        # 负半径: 取大圆弧(>180度),圆心在另一侧
        
        if arc_command in ['G2', 'G02']:  # 顺时针
            # 标准情况: 圆心在右侧
            perp_x = dy / perp_length
            perp_y = -dx / perp_length
            if radius < 0:  # 大圆弧，圆心翻转到左侧
                perp_x = -perp_x
                perp_y = -perp_y
        else:  # G3/G03 逆时针
            # 标准情况: 圆心在左侧
            perp_x = -dy / perp_length
            perp_y = dx / perp_length
            if radius < 0:  # 大圆弧，圆心翻转到右侧
                perp_x = -perp_x
                perp_y = -perp_y
        
        # 计算圆心位置
        center_x = mid_x + height * perp_x
        center_y = mid_y + height * perp_y
        
        # 验证半径
        calc_radius_start = math.sqrt((start_x - center_x)**2 + (start_y - center_y)**2)
        calc_radius_end = math.sqrt((end_x - center_x)**2 + (end_y - center_y)**2)
        radius_diff_start = abs(calc_radius_start - actual_radius)
        radius_diff_end = abs(calc_radius_end - actual_radius)
        
        if radius_diff_start > 0.001 or radius_diff_end > 0.001:  # 允许1微米误差
            self.log_message(f"半径验证失败: 起点半径={calc_radius_start:.4f}, 终点半径={calc_radius_end:.4f}, 指定半径={actual_radius:.4f}")
            self.log_message(f"起点误差={radius_diff_start:.6f}, 终点误差={radius_diff_end:.6f}")
            # 不返回None，继续使用计算的圆心（可能是数值精度问题）
        
        self.log_message(f"圆心计算: ({center_x:.4f}, {center_y:.4f}), 半径={actual_radius:.4f}")
        return center_x, center_y
    
    def subdivide_arc(self, end_x, end_y, params, command):
        """细分圆弧为多个点 - 支持R格式和I/J格式"""
        if self.arc_plane != 'G17':  # 仅支持XY平面
            self.log_message(f"警告: 当前仅支持G17(XY平面)圆弧细分,检测到{self.arc_plane},跳过细分")
            return []
        
        arc_command = command  # 统一变量名
        start_point = self.get_arc_start_point()
        start_x = start_point['X']
        start_y = start_point['Y']
        
        # 检查起点终点是否重合
        if abs(start_x - end_x) < 0.001 and abs(start_y - end_y) < 0.001:
            self.log_message("警告: 圆弧起点和终点重合，无法细分")
            return []
        
        # 判断使用I/J格式还是R格式
        if 'I' in params or 'J' in params:
            # I/J格式
            i_offset = params.get('I', 0.0)
            j_offset = params.get('J', 0.0)
            result = self.calculate_arc_center_ij(end_x, end_y, i_offset, j_offset, arc_command)
            if result is None:
                self.log_message("无法计算I/J格式圆弧圆心")
                return []
            cx, cy, start_radius = result
        elif 'R' in params:
            # R格式
            radius = params['R']
            center = self.calculate_arc_center(end_x, end_y, radius, arc_command)
            if center is None:
                self.log_message("无法计算R格式圆弧圆心")
                return []
            cx, cy = center
            start_radius = abs(radius)
        else:
            self.log_message("错误: 圆弧指令缺少R或I/J参数")
            return []
        
        # 计算起点和终点角度
        start_angle = math.atan2(start_y - cy, start_x - cx)
        end_angle = math.atan2(end_y - cy, end_x - cx)
        
        # 计算角度变化（不使用normalize，直接处理）
        angle_diff = end_angle - start_angle
        
        # 调整圆弧方向
        if arc_command in ['G2', 'G02']:  # 顺时针
            if angle_diff > 0:
                angle_diff -= 2 * math.pi
            angle_change = angle_diff  # 保持负值表示顺时针
        else:  # G3/G03 逆时针
            if angle_diff < 0:
                angle_diff += 2 * math.pi
            angle_change = angle_diff  # 保持正值表示逆时针
        
        # 计算细分点数量
        total_angle = abs(angle_change)
        resolution_rad = math.radians(self.angular_resolution)
        num_points = max(2, int(total_angle / resolution_rad) + 1)
        
        # 检查是否需要细分：如果角度小于等于分辨率，或接近分辨率(含容差)，不进行细分
        if total_angle <= resolution_rad + 1e-9:
            self.log_message(f"圆弧角度({math.degrees(total_angle):.4f}度)小于等于分辨率({self.angular_resolution}度)，不细分")
            return None  # 返回None表示不需要细分
        
        angle_step = angle_change / (num_points - 1)
        
        # 生成中间点（优化：只保留必要的点）
        points = []
        for i in range(1, num_points):
            angle = start_angle + i * angle_step
            px = cx + start_radius * math.cos(angle)
            py = cy + start_radius * math.sin(angle)
            # 四舍五入到3位小数，减少文件大小
            points.append((round(px, 3), round(py, 3)))
        
        self.log_message(f"圆弧细分成功: 生成{len(points)}个点")
        return points
    
    # 在 generate_g1_lines 方法中确保输出F值
    def generate_g1_lines(self, base_line_number, points, feed_changed):
        """生成G1指令 - 使用原始行号加小数部分，仅在进给变化时输出F"""
        lines = []
        current_z = self.last_axis_update.get('Z', None)
        
        # 优化：只在第一个点输出Z和F值，后续点省略
        for i, point in enumerate(points):
            x, y = point
            # 生成带小数部分的行号（如果有原始行号）
            if base_line_number:
                # 移除原始行号的"N"前缀
                base_num = base_line_number[1:] if base_line_number.startswith('N') else base_line_number
                # 添加小数部分
                line_num = f"N{base_num}.{i+1}"
                line = f"{line_num} G1 X{x:.3f} Y{y:.3f}"
            else:
                # 如果没有行号，直接生成指令
                line = f"G1 X{x:.3f} Y{y:.3f}"
            
            # 只在第一个点添加Z和F值，减少文件大小
            if i == 0:
                if current_z is not None:
                    line += f" Z{current_z:.3f}"
                    
                # 仅当进给速度有变化时输出F
                if feed_changed and self.feed_rate is not None:
                    line += f" F{self.feed_rate:.1f}"
                
            lines.append(line)
        
        return lines
    
    def process_gcode_path(self, input_path, output_path):
        """处理G代码文件路径 - 独立跟踪各轴位置"""
        start_time = time.time()
        
        input_path = Path(input_path)
        output_path = Path(output_path)
        
        if not input_path.exists():
            raise FileNotFoundError(f"输入文件不存在: {input_path}")
        
        self.output_lines = []
        # 初始化各轴位置
        self.axis_pos = defaultdict(float)
        self.last_axis_update = defaultdict(float)
        for axis in ['X', 'Y', 'Z']:
            self.axis_pos[axis] = 0.0
            self.last_axis_update[axis] = 0.0
        
        self.arc_plane = 'G17'
        self.distance_mode = 'G90'
        self.feed_rate = None
        self.last_motion_command = None
        self.current_line_number = None
        
        # 检测文件编码
        with open(input_path, 'rb') as f:
            raw_data = f.read(4096)
            result = chardet.detect(raw_data)
            file_encoding = result.get('encoding') if result else 'gbk'
        
        file_encoding = (result or {}).get('encoding') or 'gbk'
        confidence = (result or {}).get('confidence', 0)
        self.log_message(f"检测到文件编码: {file_encoding} (置信度: {confidence:.2f})")
        
        # 处理文件
        with open(input_path, 'r', encoding=file_encoding, errors='replace') as f:
            for line in f:
                self.process_line(line)
        
        # 写入输出文件
        with open(output_path, 'w', encoding='utf-8') as f:
            for line in self.output_lines:
                f.write(line + '\n')
        
        # 性能统计
        elapsed_time = time.time() - start_time
        input_size = os.path.getsize(input_path) / 1024 / 1024  # MB
        output_size = os.path.getsize(output_path) / 1024 / 1024  # MB
        self.log_message(f"\n处理完成！")
        self.log_message(f"处理时间: {elapsed_time:.2f}秒")
        self.log_message(f"输入文件大小: {input_size:.2f}MB")
        self.log_message(f"输出文件大小: {output_size:.2f}MB")
        self.log_message(f"压缩比: {output_size/input_size:.2f}x")
        
        return output_path
    
    # 在 process_line 方法中确保模态F值被正确处理
    def process_line(self, line):
        """处理单行G代码 - 使用原始行号加小数部分，保留模态F值"""
        original_line = line.strip()
        
        # 保留注释和空行
        if not original_line or original_line.startswith('(') or original_line.startswith('%'):
            self.output_lines.append(original_line)
            return
        
        # 处理带行号的指令
        line_number, command, params = self.parse_gcode_line(original_line)
        self.current_line_number = line_number  # 保存当前行号
        
        # 处理模态命令:如果只有参数没有命令,使用上一次的运动命令
        if command is None and params and self.last_motion_command in ['G0', 'G00', 'G1', 'G01', 'G2', 'G02', 'G3', 'G03']:
            command = self.last_motion_command
            # 安全检查:如果是圆弧命令但缺少圆弧参数,不使用模态命令
            if command in ['G2', 'G02', 'G3', 'G03'] and 'R' not in params and 'I' not in params and 'J' not in params:
                self.log_message(f"警告: 圆弧模态命令缺少R/I/J参数,跳过: {original_line}")
                command = None
        
        # 处理F值(模态值)
        prev_feed = self.feed_rate
        feed_changed = False
        if 'F' in params:
            new_feed = params['F']
            feed_changed = (prev_feed is None) or (abs(new_feed - prev_feed) > 1e-6)
            self.feed_rate = new_feed
            self.log_message(f"设置进给速率: F{self.feed_rate:.1f}")
        
        # 处理特殊命令
        if command in ['G17', 'G18', 'G19']:
            self.arc_plane = command
            self.log_message(f"设置加工平面: {command}")
            self.output_lines.append(original_line)
            return
        
        if command in ['G90', 'G91']:
            self.distance_mode = command
            self.log_message(f"设置距离模式: {command}")
            self.output_lines.append(original_line)
            return
        
        # 处理移动命令
        if command in ['G0', 'G00', 'G1', 'G01', 'G2', 'G02', 'G3', 'G03']:
            self.last_motion_command = command
            
            # 如果是圆弧指令
            if command in ['G2', 'G02', 'G3', 'G03']:
                # 获取圆弧参数（不更新位置）
                end_x = params.get('X', self.last_axis_update['X'])
                end_y = params.get('Y', self.last_axis_update['Y'])
                
                # 检查是否有圆弧参数（R或I/J）
                has_arc_params = 'R' in params or 'I' in params or 'J' in params
                
                if not has_arc_params:
                    self.log_message("错误: 圆弧指令缺少R或I/J参数")
                    self.output_lines.append(original_line)
                    # 圆弧指令执行后更新位置
                    self.update_axis_position(params)
                    return
                
                self.log_message(f"处理圆弧指令: {original_line}")
                points = self.subdivide_arc(end_x, end_y, params, command)
                if points is not None and len(points) > 0:
                    # 有细分点，使用原始行号生成细分指令（保留F值）
                    g1_lines = self.generate_g1_lines(self.current_line_number, points, feed_changed)
                    self.output_lines.extend(g1_lines)
                    
                    # 圆弧细分后更新位置到终点
                    update_params = {'X': end_x, 'Y': end_y}
                    if 'Z' in params:
                        update_params['Z'] = params['Z']
                    self.update_axis_position(update_params)
                else:
                    # 不需要细分或无法细分，保留原指令
                    if points is None:
                        self.log_message("圆弧不需要细分，保留原指令")
                    else:
                        self.log_message("圆弧细分失败，保留原指令")
                    self.output_lines.append(original_line)
                    # 圆弧指令执行后更新位置
                    self.update_axis_position(params)
            else:
                # 直线移动，保留原指令
                self.output_lines.append(original_line)
                # 直线指令执行后更新位置
                self.update_axis_position(params)
            return
        
        # 其他指令处理
        self.output_lines.append(original_line)
        # 其他指令也可能更新位置（如G92等）
        if params:
            self.update_axis_position(params)
            
class GCodeSubdividerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("G代码圆弧细分工具")
        
        # 设置窗口初始大小和最小尺寸
        self.root.geometry("900x700")
        self.root.minsize(800, 600)
        
        # 居中显示窗口
        self.center_window()
        
        # 创建主框架，使用canvas+scrollbar实现滚动
        main_canvas = tk.Canvas(root)
        scrollbar = ttk.Scrollbar(root, orient="vertical", command=main_canvas.yview)
        scrollable_frame = ttk.Frame(main_canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: main_canvas.configure(scrollregion=main_canvas.bbox("all"))
        )
        
        main_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        main_canvas.configure(yscrollcommand=scrollbar.set)
        
        # 鼠标滚轮支持
        def _on_mousewheel(event):
            main_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        main_canvas.bind_all("<MouseWheel>", _on_mousewheel)
        
        main_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # 创建主框架
        main_frame = ttk.Frame(scrollable_frame, padding="20")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 处理模式选择
        mode_frame = ttk.Frame(main_frame)
        mode_frame.pack(fill=tk.X, pady=5)
        
        self.processing_mode = tk.StringVar(value="single")
        ttk.Radiobutton(mode_frame, text="单文件处理", variable=self.processing_mode, value="single").pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(mode_frame, text="批量处理", variable=self.processing_mode, value="batch").pack(side=tk.LEFT, padx=10)
        
        # 单文件处理区域
        self.single_frame = ttk.Frame(main_frame)
        self.single_frame.pack(fill=tk.X, pady=5)
        
        # 输入文件选择
        input_frame = ttk.Frame(self.single_frame)
        input_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(input_frame, text="输入文件:", width=10).pack(side=tk.LEFT)
        self.input_path = tk.StringVar()
        input_entry = ttk.Entry(input_frame, textvariable=self.input_path)
        input_entry.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        ttk.Button(input_frame, text="浏览...", command=self.browse_input).pack(side=tk.LEFT)
        
        # 输出文件选择
        output_frame = ttk.Frame(self.single_frame)
        output_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(output_frame, text="输出文件:", width=10).pack(side=tk.LEFT)
        self.output_path = tk.StringVar()
        output_entry = ttk.Entry(output_frame, textvariable=self.output_path)
        output_entry.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        ttk.Button(output_frame, text="浏览...", command=self.browse_output).pack(side=tk.LEFT)
        
        # 批量处理区域（初始隐藏）
        self.batch_frame = ttk.Frame(main_frame)
        
        # 批量输入选择
        batch_input_frame = ttk.Frame(self.batch_frame)
        batch_input_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(batch_input_frame, text="输入路径:", width=10).pack(side=tk.LEFT)
        self.batch_input_path = tk.StringVar()
        batch_input_entry = ttk.Entry(batch_input_frame, textvariable=self.batch_input_path)
        batch_input_entry.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        ttk.Button(batch_input_frame, text="浏览...", command=self.browse_batch_input).pack(side=tk.LEFT)
        
        # 批量输出选择
        batch_output_frame = ttk.Frame(self.batch_frame)
        batch_output_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(batch_output_frame, text="输出目录:", width=10).pack(side=tk.LEFT)
        self.batch_output_dir = tk.StringVar()
        batch_output_entry = ttk.Entry(batch_output_frame, textvariable=self.batch_output_dir)
        batch_output_entry.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)
        ttk.Button(batch_output_frame, text="浏览...", command=self.browse_batch_output).pack(side=tk.LEFT)
        
        # 文件后缀过滤
        filter_frame = ttk.Frame(self.batch_frame)
        filter_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(filter_frame, text="文件后缀:").pack(side=tk.LEFT)
        self.file_ext = tk.StringVar(value="*.nc;*.cnc;*.gcode;*.txt")
        filter_entry = ttk.Entry(filter_frame, textvariable=self.file_ext, width=30)
        filter_entry.pack(side=tk.LEFT, padx=5)
        ttk.Label(filter_frame, text="(多个后缀用分号分隔)").pack(side=tk.LEFT)
        
        # 设置区域
        settings_frame = ttk.LabelFrame(main_frame, text="处理设置")
        settings_frame.pack(fill=tk.X, pady=10)
        
        # 分辨率设置
        resolution_frame = ttk.Frame(settings_frame)
        resolution_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(resolution_frame, text="角度分辨率(度):", width=15).pack(side=tk.LEFT)
        self.resolution = tk.DoubleVar(value=5.0)
        resolution_entry = ttk.Entry(resolution_frame, textvariable=self.resolution, width=10)
        resolution_entry.pack(side=tk.LEFT, padx=5)
        ttk.Label(resolution_frame, text="(推荐3-10度)").pack(side=tk.LEFT, padx=5)
        
        # 日志级别
        log_frame = ttk.Frame(settings_frame)
        log_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(log_frame, text="日志级别:", width=15).pack(side=tk.LEFT)
        self.log_level = tk.StringVar(value="详细")
        log_combo = ttk.Combobox(log_frame, textvariable=self.log_level, width=10, state="readonly")
        log_combo['values'] = ('简洁', '详细', '调试')
        log_combo.pack(side=tk.LEFT, padx=5)
        
        # 操作按钮
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(pady=20)
        
        self.process_btn = ttk.Button(button_frame, text="处理文件", command=self.start_processing)
        self.process_btn.pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="清除日志", command=self.clear_log).pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="打开输出目录", command=self.open_output_dir).pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="退出", command=root.quit).pack(side=tk.LEFT, padx=10)
        
        # 进度条
        self.progress = ttk.Progressbar(main_frame, orient=tk.HORIZONTAL, length=400, mode='determinate')
        self.progress.pack(pady=5, fill=tk.X)
        self.progress.pack_forget()  # 初始隐藏
        
        # 日志区域
        log_frame = ttk.LabelFrame(main_frame, text="处理日志")
        log_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        self.log_text = tk.Text(log_frame, height=15, wrap=tk.WORD)
        log_scrollbar = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_text.yview)
        log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(yscrollcommand=log_scrollbar.set)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.log_text.config(state=tk.DISABLED)
        
        # 状态栏
        self.status_var = tk.StringVar(value="就绪")
        status_bar = ttk.Label(root, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 绑定事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.processing_mode.trace_add("write", self.toggle_processing_mode)
        
        # 设置初始模式
        self.toggle_processing_mode()
        input_entry.focus_set()
    
    def center_window(self):
        """将窗口居中显示"""
        self.root.update_idletasks()
        width = self.root.winfo_width()
        height = self.root.winfo_height()
        x = (self.root.winfo_screenwidth() // 2) - (width // 2)
        y = (self.root.winfo_screenheight() // 2) - (height // 2)
        self.root.geometry(f'{width}x{height}+{x}+{y}')
    
    def format_angle_suffix(self, angle):
        """格式化角度后缀：整数直接显示，小数用'p'代替小数点"""
        # 检查是否为整数（包括5.0这种情况）
        if float(angle).is_integer():
            return f"_{int(angle)}"
        else:
            # 将浮点数转换为字符串并用'p'替换小数点
            angle_str = f"{angle:.4f}".rstrip('0').rstrip('.')
            return f"_{angle_str.replace('.', 'p')}"

    
    def get_output_filename(self, input_path, resolution):
        """生成带角度后缀的输出文件名"""
        input_path = Path(input_path)
        suffix = self.format_angle_suffix(resolution)
        return input_path.parent / f"{input_path.stem}_subdivided{suffix}{input_path.suffix}"
    
    def toggle_processing_mode(self, *args):
        """切换单文件/批量处理模式"""
        mode = self.processing_mode.get()
        if mode == "single":
            self.single_frame.pack(fill=tk.X, pady=5)
            self.batch_frame.pack_forget()
            self.process_btn.config(text="处理文件")
        else:
            self.single_frame.pack_forget()
            self.batch_frame.pack(fill=tk.X, pady=5)
            self.process_btn.config(text="批量处理")
    
    def browse_input(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("G代码文件", "*.nc;*.cnc;*.gcode;*.txt"), ("所有文件", "*.*")]
        )
        if file_path:
            self.input_path.set(file_path)
            if not self.output_path.get():
                # 使用带角度后缀的文件名
                resolution = self.resolution.get()
                output_file = self.get_output_filename(file_path, resolution)
                self.output_path.set(str(output_file))
    
    def browse_output(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".nc",
            filetypes=[("G代码文件", "*.nc;*.cnc;*.gcode;*.txt"), ("所有文件", "*.*")]
        )
        if file_path:
            self.output_path.set(file_path)
    
    def browse_batch_input(self):
        """选择批量处理的输入路径（文件或目录）"""
        selection = filedialog.askopenfilenames(
            title="选择多个文件或取消选择目录",
            filetypes=[("G代码文件", "*.nc;*.cnc;*.gcode;*.txt"), ("所有文件", "*.*")]
        )
        
        if selection:
            # 用户选择了文件
            self.batch_input_path.set(";".join(selection))
        else:
            # 用户取消选择文件，改为选择目录
            dir_path = filedialog.askdirectory(title="选择包含G代码文件的目录")
            if dir_path:
                self.batch_input_path.set(dir_path)
    
    def browse_batch_output(self):
        """选择批量处理的输出目录"""
        dir_path = filedialog.askdirectory(title="选择输出目录")
        if dir_path:
            self.batch_output_dir.set(dir_path)
    
    def clear_log(self):
        """清除日志内容"""
        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete(1.0, tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.status_var.set("日志已清除")
    
    def open_output_dir(self):
        """打开输出目录"""
        mode = self.processing_mode.get()
        if mode == "single":
            output_path = self.output_path.get()
            if output_path:
                output_dir = os.path.dirname(output_path)
                if output_dir and os.path.exists(output_dir):
                    os.startfile(output_dir)
                elif output_dir:
                    # 目录不存在，询问是否创建
                    if messagebox.askyesno("目录不存在", f"输出目录不存在，是否创建？\n{output_dir}"):
                        os.makedirs(output_dir, exist_ok=True)
                        os.startfile(output_dir)
                else:
                    messagebox.showinfo("信息", "无法确定输出目录")
            else:
                # 如果没有设置输出路径，尝试打开输入文件所在目录
                input_path = self.input_path.get()
                if input_path and os.path.exists(input_path):
                    input_dir = os.path.dirname(input_path)
                    if input_dir:
                        os.startfile(input_dir)
                    else:
                        os.startfile(os.getcwd())
                else:
                    messagebox.showinfo("信息", "请先选择输入文件或设置输出路径")
        else:
            output_dir = self.batch_output_dir.get()
            if output_dir:
                if os.path.exists(output_dir):
                    os.startfile(output_dir)
                else:
                    # 目录不存在，询问是否创建
                    if messagebox.askyesno("目录不存在", f"输出目录不存在，是否创建？\n{output_dir}"):
                        os.makedirs(output_dir, exist_ok=True)
                        os.startfile(output_dir)
            else:
                # 尝试打开输入路径
                input_path = self.batch_input_path.get()
                if input_path:
                    if os.path.isdir(input_path):
                        os.startfile(input_path)
                    elif os.path.isfile(input_path):
                        os.startfile(os.path.dirname(input_path))
                    else:
                        messagebox.showinfo("信息", "请先设置输出目录")
                else:
                    messagebox.showinfo("信息", "请先设置输入路径或输出目录")
    
    def log_message(self, message):
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, message + "\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)
        self.status_var.set(message)
        self.root.update()
    
    def start_processing(self):
        """开始处理文件（单文件或批量）"""
        mode = self.processing_mode.get()
        if mode == "single":
            self.process_file()
        else:
            self.process_batch()
    
    def process_file(self):
        """处理单个文件"""
        input_file = self.input_path.get()
        output_file = self.output_path.get()
        resolution = self.resolution.get()
        
        if not input_file:
            messagebox.showerror("错误", "请选择输入文件")
            return
            
        if not output_file:
            # 如果没有指定输出文件，自动生成带角度后缀的文件名
            output_file = self.get_output_filename(input_file, resolution)
            self.output_path.set(str(output_file))
        
        try:
            self.log_message(f"开始处理文件: {input_file}")
            self.log_message(f"输出路径: {output_file}")
            self.log_message(f"使用分辨率: {resolution}度")
            
            # 处理文件
            subdivider = ArcSubdivider(angular_resolution=resolution, log_message=self.log_message)
            output_path = subdivider.process_gcode_path(input_file, output_file)
            
            self.log_message("处理成功! 文件已保存")
            messagebox.showinfo("成功", f"处理完成!\n输出文件: {output_path}")
        except Exception as e:
            error_msg = f"处理失败: {str(e)}"
            self.log_message(error_msg)
            messagebox.showerror("错误", error_msg)
            import traceback
            traceback.print_exc()
    
    def process_batch(self):
        """批量处理多个文件或目录"""
        input_path = self.batch_input_path.get()
        output_dir = self.batch_output_dir.get()
        resolution = self.resolution.get()
        file_extensions = [ext.strip() for ext in self.file_ext.get().split(';') if ext.strip()]
        
        if not input_path:
            messagebox.showerror("错误", "请选择输入文件或目录")
            return
            
        if not output_dir:
            messagebox.showerror("错误", "请指定输出目录")
            return
        
        # 获取文件列表
        file_paths = []
        if os.path.isdir(input_path):
            # 处理目录
            input_dir = input_path
            self.log_message(f"开始批量处理目录: {input_dir}")
            self.log_message(f"输出目录: {output_dir}")
            self.log_message(f"文件后缀: {', '.join(file_extensions)}")
            
            # 遍历目录收集文件
            for root, _, files in os.walk(input_dir):
                for file in files:
                    if any(file.lower().endswith(ext.lower().lstrip('*')) for ext in file_extensions):
                        file_paths.append(os.path.join(root, file))
        elif ';' in input_path:
            # 处理多个文件
            file_paths = input_path.split(';')
        else:
            # 处理单个文件
            file_paths = [input_path]
        
        if not file_paths:
            messagebox.showinfo("信息", "没有找到符合条件的文件")
            return
        
        # 创建输出目录
        os.makedirs(output_dir, exist_ok=True)
        
        # 显示进度条
        self.progress.pack(pady=5, fill=tk.X)
        self.progress["value"] = 0
        self.progress["maximum"] = len(file_paths)
        
        # 禁用处理按钮
        self.process_btn.config(state=tk.DISABLED)
        
        # 在单独的线程中处理批量任务
        threading.Thread(target=self.run_batch_processing, args=(file_paths, output_dir, resolution), daemon=True).start()
    
    def run_batch_processing(self, file_paths, output_dir, resolution):
        """执行批量处理任务 - 优化内存使用"""
        total_files = len(file_paths)
        success_count = 0
        fail_count = 0
        
        for i, input_file in enumerate(file_paths):
            # 每个文件使用新的ArcSubdivider实例
            subdivider = None
            try:
                # 更新进度和状态
                self.status_var.set(f"处理中: {i+1}/{total_files} - {os.path.basename(input_file)}")
                self.progress["value"] = i
                self.root.update()
                
                # 创建带角度后缀的输出文件名
                output_file = self.get_output_filename(input_file, resolution)
                output_file = os.path.join(output_dir, output_file.name)
                
                # 处理文件 - 为每个文件创建新的实例
                self.log_message(f"\n处理文件 {i+1}/{total_files}: {os.path.basename(input_file)}")
                subdivider = ArcSubdivider(angular_resolution=resolution, log_message=self.log_message)
                output_path = subdivider.process_gcode_path(input_file, output_file)
                
                self.log_message(f"处理成功: {output_path}")
                success_count += 1
                
                # 显式删除实例以释放内存
                del subdivider
                subdivider = None
                
                # 强制垃圾回收
                import gc
                gc.collect()
                
            except Exception as e:
                self.log_message(f"处理失败: {os.path.basename(input_file)} - {str(e)}")
                fail_count += 1
                
                # 确保实例被删除
                if subdivider is not None:
                    del subdivider
                    subdivider = None
        
        # 更新进度条完成
        self.progress["value"] = total_files
        self.status_var.set(f"批量处理完成! 成功: {success_count}, 失败: {fail_count}")
        
        # 显示摘要
        summary = f"\n批量处理完成!\n总文件数: {total_files}\n成功: {success_count}\n失败: {fail_count}"
        self.log_message(summary)
        messagebox.showinfo("批量处理完成", summary)
        
        # 恢复处理按钮
        self.process_btn.config(state=tk.NORMAL)
        # 隐藏进度条
        self.progress.pack_forget()
        
    def on_close(self):
        """窗口关闭时的处理"""
        self.root.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    app = GCodeSubdividerApp(root)
    root.mainloop()
