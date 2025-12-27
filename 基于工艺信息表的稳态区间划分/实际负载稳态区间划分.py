# actual_load_analysis.py
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import math
import re
import os
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
import matplotlib
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
import collections
import pandas as pd
from typing import List, Tuple, Union
from datetime import datetime
import sys
import gc
from scipy.signal import butter, filtfilt
import chardet
import copy

# 判断是否在打包环境中运行
if getattr(sys, 'frozen', False):
    # 打包环境 - 使用临时解压目录
    base_dir = getattr(sys, '_MEIPASS', os.path.abspath(os.path.dirname(__file__)))
else:
    # 正常环境 - 使用脚本所在目录
    base_dir = os.path.dirname(os.path.abspath(__file__))

# 设置黑体字体路径
simhei_path = os.path.join(base_dir, 'SimHei.ttf')

# 检查字体文件是否存在
if os.path.exists(simhei_path):
    # 添加字体到matplotlib
    import matplotlib.font_manager as fm
    fm.fontManager.addfont(simhei_path)
    
    # 设置matplotlib使用中文字体
    plt.rcParams['font.family'] = 'sans-serif'
    plt.rcParams['font.sans-serif'] = ['SimHei']
    plt.rcParams['axes.unicode_minus'] = False
else:
    print(f"警告: 字体文件 {simhei_path} 未找到，将使用系统默认字体")

# 设置matplotlib使用中文字体
matplotlib.rcParams['font.sans-serif'] = ['SimHei']  # 使用黑体
matplotlib.rcParams['axes.unicode_minus'] = False    # 解决负号显示问题

class ActualLoadAnalysis:
    def __init__(self, root, csv_file=None, txt_file=None):
        self.root = root
        self.root.title("实际负载稳态区间划分工具")
        
        # 获取屏幕尺寸并设置自适应窗口大小
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 计算合适的窗口大小
        max_width, max_height = 1400, 900
        min_width, min_height = 1000, 700
        
        window_width = min(max_width, max(min_width, int(screen_width * 0.8)))
        window_height = min(max_height, max(min_height, int(screen_height * 0.8)))
        
        # 计算居中位置
        center_x = (screen_width - window_width) // 2
        center_y = (screen_height - window_height) // 2
        
        # 设置窗口大小和位置
        self.root.geometry(f"{window_width}x{window_height}+{center_x}+{center_y}")
        self.root.minsize(min_width, min_height)
        self.root.resizable(True, True)
        
        self.external_csv_file = csv_file
        self.external_txt_file = txt_file
        self.program_mapping = {}  # {program_id: {'name': str, 'tools_list': [{'tool_id': str, 'start': int, 'end': int}]}}
        self.current_program_id = None
        self.current_tool_key = None  # 格式: tool_id_index
        self.programs_data = {}  # {program_id: {tool_key: {...}}}
        self.analyzed_results = {}
        self.data_source = tk.StringVar(value='电流')  # 数据源选择：电流、vgpro功率、边缘模块功率
        
        self.actual_load_input_path = tk.StringVar()
        self.reduce_interval_actual_load = tk.BooleanVar(value=True)
        self.cutoff_freq = tk.DoubleVar(value=0.1)
        self.filter_order = tk.IntVar(value=4)
        self.filtered_data = None
        self.is_filtered = False
        self.original_xlim = None
        self.original_ylim = None
        self.scroll_cid = None
        self.press_cid = None
        self.motion_cid = None
        self.release_cid = None
        self.is_panning = False
        self.pan_start = None
        self.zoom_factor = 1.2
        self.current_adjustment_ratio = 1.2
        self.actual_load_data = []
        self.actual_load_line_numbers = []
        self.actual_load_point_indices = []
        self.actual_load_x_positions = []
        self.actual_load_unique_line_numbers = []
        self.actual_load_intervals = []
        self.actual_load_interval_values = []
        self.current_intervals = []
        self.auto_sensitivity = tk.DoubleVar(value=1.0)
        self.adjustment_mode = False
        self.selected_intervals = []
        self.dragging_boundary = None
        self.interval_boundary_lines = []
        self.adjustment_cid = None
        self.adjustment_motion_cid = None
        self.adjustment_release_cid = None
        # 区间合并/模式控制: 'all_small' | 'large_coverage'
        # 'all_small' : 返回检测到的所有小区间（更敏感，保留原始小区间）
        # 'large_coverage'现在的有个问题，划分前理想值显示为1.155，划分后显示为1.055，怎么保存到rg文件里的是1.165，都对不上，我需要保存和页面显示的是划分后区间平均值的平均值 : 优先合并/扩展区间以提升覆盖率（默认，减少只覆盖波峰的小区间）
        self.interval_mode = 'large_coverage'
        # 在 large_coverage 模式下，目标覆盖率（0-1），算法会尽量合并邻近区间以达到该覆盖率
        # 默认提高到 0.90，优先保证覆盖率更高（可在UI调整回更严格设置）
        self.target_coverage = 0.90
        # 合并时允许的最大间隙比例（相对于数据长度），用于控制合并的激进程度
        self.max_merge_gap_ratio = 0.02
        # 激进合并允许的更大间隙比例（第二阶段），若初始合并未达到目标覆盖率可使用
        self.aggressive_merge_gap_ratio = 0.10
        # 在激进扩展阶段，每个区块允许向外扩展的最大比例（相对于 min_len）
        # 提高到 1.0，允许按照平均区间长度向外扩展，能更快提升覆盖率
        self.expand_ratio_for_coverage = 1.0
        
        self.create_interface()
        self.init_figure()
        self.root.bind("<Configure>", self.on_window_resize)
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.root.after(100, self.adjust_figure_size)
        if self.external_csv_file and self.external_txt_file:
            self.status_var_actual_load.set(f"⏳ 准备加载数据: {os.path.basename(self.external_csv_file)}")
            self.root.after(200, self.load_external_files)
        else:
            self.status_var_actual_load.set("⚠️ 未传入数据文件，请手动加载")
    
    def load_external_files(self):
        """加载外部传入的CSV和TXT文件（带进度窗口）"""
        try:
            progress_window = tk.Toplevel(self.root)
            progress_window.title("加载数据")
            progress_window.geometry("400x120")
            progress_window.transient(self.root)
            progress_window.grab_set()
            progress_window.update_idletasks()
            x = (progress_window.winfo_screenwidth() // 2) - 200
            y = (progress_window.winfo_screenheight() // 2) - 60
            progress_window.geometry(f"400x120+{x}+{y}")
            status_label = tk.Label(progress_window, text="正在加载数据，请稍候...", font=('Microsoft YaHei', 12))
            status_label.pack(pady=20)
            progress_bar = ttk.Progressbar(progress_window, mode='indeterminate', length=350)
            progress_bar.pack(pady=10)
            progress_bar.start(10)
            self.status_var_actual_load.set("正在加载数据...")
            progress_window.update()
            status_label.config(text="正在解析程序映射文件...")
            progress_window.update()
            self.parse_program_mapping(self.external_txt_file)
            status_label.config(text="正在解析CSV数据文件（可能需要几秒钟）...")
            progress_window.update()
            self.parse_csv_data(self.external_csv_file)
            status_label.config(text="正在更新界面...")
            progress_window.update()
            self.update_program_selector()
            if self.program_mapping:
                first_program_id = list(self.program_mapping.keys())[0]
                program_info = self.program_mapping[first_program_id]
                program_name = program_info['name'] if isinstance(program_info, dict) else program_info
                self.program_selector.set(f"{program_name} ({first_program_id})")
                self.on_program_selected(None)
            progress_bar.stop()
            progress_window.destroy()
            self.status_var_actual_load.set(f"✅ 成功加载 {len(self.program_mapping)} 个程序")
            
            # 显示所有已划分的区间汇总
            self.update_all_intervals_summary()
        except Exception as e:
            # 确保进度窗口被关闭
            if 'progress_window' in locals():
                try:
                    progress_window.destroy()
                except:
                    pass
            messagebox.showerror("加载错误", f"加载外部文件时发生错误:\n{str(e)}")
            self.status_var_actual_load.set("❌ 加载失败")
    
    def parse_program_mapping(self, txt_file):
        """解析TXT文件获取程序映射关系（支持刀具信息）
        新格式每行一个刀具: 程序名:程序号:刀具号:起始行-终止行;
        例如: O999:384000036:T3:18-64;
        注意: tools_list 保持txt文件顺序,允许重复的刀具号
        """
        with open(txt_file, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        for line in lines:
            line = line.strip()
            # 移除末尾的分号
            if line.endswith(';'):
                line = line[:-1]
            
            if not line or ':' not in line:
                continue
            
            # 分割行获取信息: 程序名:程序号:刀具号:行号范围
            parts = line.split(':')
            if len(parts) < 4:
                continue
            
            program_name = parts[0].strip()
            program_id = parts[1].strip()
            tool_id = parts[2].strip()
            range_str = parts[3].strip()
            
            # 解析行号范围
            if '-' not in range_str:
                continue
            
            range_parts = range_str.split('-')
            try:
                start_line = int(range_parts[0].strip())
                end_line = int(range_parts[1].strip())
            except ValueError:
                continue
            
            # 添加到映射中
            if program_id not in self.program_mapping:
                self.program_mapping[program_id] = {
                    'name': program_name,
                    'tools_list': []  # 使用列表保持顺序,允许重复
                }
            
            # 添加刀具信息到列表(按txt顺序,允许重复)
            self.program_mapping[program_id]['tools_list'].append({
                'tool_id': tool_id,
                'start': start_line,
                'end': end_line
            })
    
    def parse_csv_data(self, csv_file):
        """解析CSV文件并按程序号和刀具分组数据
        CSV格式：第1列=电流，第2列=vgpro功率，第3列=边缘模块功率，第4列=行号，第5列=程序号
        """
        # 读取CSV文件（5列数据）
        df = pd.read_csv(csv_file, header=None, 
                        dtype={0: 'float32', 1: 'float32', 2: 'float32', 3: 'int32', 4: str},
                        engine='c')
        
        # 取绝对值（电流、两种功率）
        df[0] = np.abs(df[0].values)
        df[1] = np.abs(df[1].values)
        df[2] = np.abs(df[2].values)
        
        # 按程序号分组
        grouped = df.groupby(4, sort=False)
        
        processed_count = 0
        for program_id, program_info in self.program_mapping.items():
            if program_id not in grouped.groups:
                continue
            
            program_data = grouped.get_group(program_id)
            program_name = program_info['name']
            tools_list = program_info.get('tools_list', [])
            
            # 为每个刀具创建数据
            if program_id not in self.programs_data:
                self.programs_data[program_id] = {}
            
            # 遍历tools_list,使用索引区分相同刀具的不同出现
            for idx, tool_info in enumerate(tools_list):
                tool_id = tool_info['tool_id']
                start_line = tool_info['start']
                end_line = tool_info['end']
                
                # 生成唯一的工具键: tool_id + 索引
                tool_key = f"{tool_id}_{idx}"
                
                # 筛选该刀具的行号范围
                mask = (program_data[3] >= start_line) & (program_data[3] <= end_line)
                tool_data = program_data[mask]
                
                if len(tool_data) == 0:
                    continue
                
                # 提取三种数据源
                current_data = tool_data[0].values.astype('float64')
                vgpro_power_data = tool_data[1].values.astype('float64')
                edge_power_data = tool_data[2].values.astype('float64')
                line_numbers_array = tool_data[3].values.astype('float32')
                
                # 计算点索引
                point_indices = tool_data.groupby(3, sort=False).cumcount().values
                
                unique_line_numbers, counts = np.unique(line_numbers_array, return_counts=True)
                unique_line_numbers_sorted = np.sort(unique_line_numbers)
                
                # 计算X轴位置
                if len(unique_line_numbers) == 1:
                    n = float(unique_line_numbers[0])
                    total_points = len(line_numbers_array)
                    x_positions = n + np.arange(total_points, dtype='float32') / total_points
                else:
                    line_point_counts_dict = dict(zip(unique_line_numbers, counts))
                    point_counts_array = np.array([line_point_counts_dict[ln] for ln in line_numbers_array], dtype='float32')
                    x_positions = line_numbers_array + point_indices / point_counts_array
                
                # 存储数据（包含三种数据源）
                self.programs_data[program_id][tool_key] = {
                    'name': program_name,
                    'tool_id': tool_id,
                    'tool_key': tool_key,
                    'start_line': start_line,
                    'end_line': end_line,
                    'current_data': current_data,
                    'vgpro_power_data': vgpro_power_data,
                    'edge_power_data': edge_power_data,
                    'data': current_data,  # 默认使用电流数据
                    'average': float(current_data.mean()),
                    'line_numbers': line_numbers_array,
                    'point_indices': point_indices,
                    'x_positions': x_positions,
                    'unique_line_numbers': unique_line_numbers_sorted,
                    'intervals': [],
                    'interval_values': [],
                    'filtered_data': None,
                    'is_filtered': False,
                    'adjustment_ratio': 1.2,  # 每个刀具独立的优化倍率
                    'auto_sensitivity': 1.0,  # 每个刀具独立的灵敏度
                    'cutoff_freq': 0.1,
                    'filter_order': 4,
                }
                processed_count += 1
        
        del df
        del grouped
        gc.collect()
    
    def update_program_selector(self):
        """更新程序选择下拉框"""
        if hasattr(self, 'program_selector'):
            programs = [f"{info['name']} ({pid})" for pid, info in self.program_mapping.items()]
            self.program_selector['values'] = programs
    
    def update_tool_selector(self, program_id, preserve_selection=True):
        """更新刀具选择下拉框，按txt顺序显示，允许重复刀具
        
        Args:
            program_id: 程序ID
            preserve_selection: 是否保持当前选择（避免触发事件）
        """
        if not hasattr(self, 'tool_selector'):
            return
        
        if program_id not in self.program_mapping:
            self.tool_selector['values'] = []
            return
        
        # 保存当前选择
        current_selection = self.tool_selector.get() if preserve_selection else None
        
        tools_list = self.program_mapping[program_id].get('tools_list', [])
        tool_options = []
        
        # 按照txt文件的原始顺序遍历(使用索引)
        for idx, tool_info in enumerate(tools_list):
            tool_id = tool_info['tool_id']
            start = tool_info['start']
            end = tool_info['end']
            tool_key = f"{tool_id}_{idx}"
            
            # 检查该刀具是否已完成区间划分
            has_intervals = False
            if program_id in self.programs_data:
                if tool_key in self.programs_data[program_id]:
                    tool_data = self.programs_data[program_id][tool_key]
                    if 'intervals' in tool_data and tool_data['intervals']:
                        has_intervals = True
            
            # 在刀具号旁边添加√标记
            check_mark = " ✓" if has_intervals else ""
            # 格式: T10 (18-64) 或 T10 (18-64) ✓
            tool_options.append(f"{tool_id} ({start}-{end}){check_mark}")
        
        self.tool_selector['values'] = tool_options
        
        # 恢复之前的选择或选择第一个
        if preserve_selection and current_selection and current_selection in tool_options:
            # 通过设置值而不是索引来避免触发事件
            self.tool_selector.set(current_selection)
        elif tool_options and not preserve_selection:
            self.tool_selector.current(0)
    
    def on_program_selected(self, event):
        """当选择程序时更新刀具列表"""
        selected = self.program_selector.get()
        if not selected:
            return
        
        import re
        match = re.search(r'\(([^)]+)\)$', selected)
        if match:
            program_id = match.group(1)
            if program_id in self.programs_data:
                # 切换程序前：自动保存当前程序的状态和区间
                if hasattr(self, 'current_program_id') and self.current_program_id:
                    self.save_current_program_state()
                    self.collect_current_program_results()
                
                # 切换程序前：如果处于微调模式，自动退出微调模式
                if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
                    self.adjustment_mode = True
                    self.toggle_adjustment_mode()
                
                # 更新刀具选择器（不保持选择，选择第一个）
                self.update_tool_selector(program_id, preserve_selection=False)
                
                # 如果有刀具，默认选择第一个刀具并加载数据
                if self.tool_selector['values']:
                    self.tool_selector.current(0)
                    self.on_tool_selected(None)
    
    def on_tool_selected(self, event):
        """当选择刀具时切换数据"""
        selected_program = self.program_selector.get()
        selected_tool = self.tool_selector.get()
        
        # 获取当前选择的刀具在下拉列表中的索引
        if not selected_tool:
            return
        
        tool_index = -1
        try:
            tool_values = self.tool_selector['values']
            tool_index = list(tool_values).index(selected_tool)
        except (ValueError, AttributeError):
            return
        
        if not selected_program or not selected_tool:
            return
        
        import re
        program_match = re.search(r'\(([^)]+)\)$', selected_program)
        tool_match = re.match(r'^([^\s]+)', selected_tool)
        
        if program_match and tool_match:
            program_id = program_match.group(1)
            tool_id = tool_match.group(1)
            
            # 根据索引构建tool_key
            tool_key = f"{tool_id}_{tool_index}"
            
            if program_id in self.programs_data and tool_key in self.programs_data[program_id]:
                # 切换刀具前：保存当前刀具的状态
                if hasattr(self, 'current_program_id') and hasattr(self, 'current_tool_key'):
                    if self.current_program_id and self.current_tool_key:
                        # 只有当切换到不同的刀具时才保存
                        if self.current_program_id != program_id or self.current_tool_key != tool_key:
                            self.save_current_program_state()
                            self.collect_current_program_results()
                
                # 切换刀具前：退出微调模式
                if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
                    self.adjustment_mode = True
                    self.toggle_adjustment_mode()
                
                self.switch_to_tool(program_id, tool_key)
    
    def on_data_source_changed(self, event):
        """当数据源改变时更新数据"""
        if not hasattr(self, 'current_program_id') or not hasattr(self, 'current_tool_key'):
            return
        
        if not self.current_program_id or not self.current_tool_key:
            return
        
        # 获取当前数据
        prog_data = self.programs_data.get(self.current_program_id, {}).get(self.current_tool_key)
        if not prog_data:
            return
        
        # 检查是否已有稳态区间划分结果
        has_intervals = (
            prog_data.get('actual_load_intervals') or 
            prog_data.get('intervals') or 
            prog_data.get('is_filtered', False)
        )
        
        # 如果已有区间划分结果,弹出警告对话框
        if has_intervals:
            from tkinter import messagebox
            result = messagebox.askyesno(
                "⚠️ 警告", 
                "当前刀具已有稳态区间划分结果!\n\n"
                "切换数据源将会清除所有已划分的区间和分析结果。\n"
                "是否确认切换数据源?",
                icon='warning'
            )
            
            # 如果用户选择"否",恢复之前的数据源选择
            if not result:
                # 恢复到之前的数据源
                current_data = prog_data['data']
                if current_data is prog_data['current_data']:
                    self.data_source.set('电流')
                elif current_data is prog_data['vgpro_power_data']:
                    self.data_source.set('vgpro功率')
                elif current_data is prog_data['edge_power_data']:
                    self.data_source.set('边缘模块功率')
                return
        
        # 根据选择的数据源切换数据
        data_source = self.data_source.get()
        if data_source == '电流':
            prog_data['data'] = prog_data['current_data']
        elif data_source == 'vgpro功率':
            prog_data['data'] = prog_data['vgpro_power_data']
        elif data_source == '边缘模块功率':
            prog_data['data'] = prog_data['edge_power_data']
        
        # 重新计算平均值
        prog_data['average'] = float(prog_data['data'].mean())
        
        # 清除旧的区间和过滤数据
        prog_data['intervals'] = []
        prog_data['interval_values'] = []
        prog_data['filtered_data'] = None
        prog_data['is_filtered'] = False
        prog_data['actual_load_intervals'] = []  # 清除稳态区间
        
        # 更新刀具选择器(移除该刀具的✓标记)
        self.update_tool_selector(self.current_program_id)
        
        # 重新加载数据到界面
        self.load_program_data_to_ui(prog_data)
    
    def switch_to_tool(self, program_id, tool_key):
        """切换到指定程序的指定刀具数据"""
        self.current_program_id = program_id
        self.current_tool_key = tool_key
        prog_data = self.programs_data[program_id][tool_key]
        
        self.load_program_data_to_ui(prog_data)
    
    def load_program_data_to_ui(self, prog_data):
        """将程序数据加载到UI"""
        self.actual_load_data = prog_data['data'] if isinstance(prog_data['data'], list) else prog_data['data'].tolist()
        self.actual_load_line_numbers = prog_data['line_numbers'] if isinstance(prog_data['line_numbers'], list) else prog_data['line_numbers'].tolist()
        self.actual_load_point_indices = prog_data['point_indices'] if isinstance(prog_data['point_indices'], list) else prog_data['point_indices'].tolist()
        self.actual_load_x_positions = prog_data['x_positions'] if isinstance(prog_data['x_positions'], list) else prog_data['x_positions'].tolist()
        self.actual_load_unique_line_numbers = prog_data['unique_line_numbers'] if isinstance(prog_data['unique_line_numbers'], list) else prog_data['unique_line_numbers'].tolist()
        self.actual_load_intervals = prog_data['intervals']
        self.actual_load_interval_values = prog_data['interval_values']
        self.filtered_data = prog_data['filtered_data']
        self.is_filtered = prog_data['is_filtered']
        self.current_intervals = prog_data['intervals']
        
        if 'adjustment_ratio' not in prog_data:
            prog_data['adjustment_ratio'] = 1.1
        self.current_adjustment_ratio = prog_data['adjustment_ratio']
        
        if hasattr(self, 'ratio_scale'):
            self.ratio_scale.set(self.current_adjustment_ratio)
        
        self.cutoff_freq.set(prog_data.get('cutoff_freq', 0.1))
        self.filter_order.set(prog_data.get('filter_order', 4))
        
        # 恢复该刀具的灵敏度和优化倍率
        self.auto_sensitivity.set(prog_data.get('auto_sensitivity', 1.0))
        saved_ratio = prog_data.get('adjustment_ratio', 1.2)
        self.current_adjustment_ratio = saved_ratio
        if hasattr(self, 'ratio_scale'):
            self.ratio_scale.set(saved_ratio)
        if hasattr(self, 'adjustment_ratio_entry'):
            self.adjustment_ratio_entry.delete(0, tk.END)
            self.adjustment_ratio_entry.insert(0, f"{saved_ratio:.3f}")
        
        # 切换数据后：确保微调模式为关闭状态
        if hasattr(self, 'adjustment_mode'):
            self.adjustment_mode = False
        if hasattr(self, 'adjustment_button'):
            self.adjustment_button.config(text="✏️ 微调")
        
        # 显示区间平均值而非整体平均值
        interval_avg = self.calculate_interval_average(prog_data)
        self.average_value_label.config(text=f"{interval_avg:.3f}")
        
        self.update_ideal_value()
        
        # 判断是否有稳态区间需要显示
        data_type = "滤波" if prog_data.get('is_filtered', False) else "原始"
        
        if self.actual_load_intervals:
            # 如果有区间，使用 plot_steady_intervals 绘制（包含区间高亮）
            self.plot_steady_intervals(data_type)
            # 显示区间信息文本
            self.update_interval_display(data_type, self.reduce_interval_actual_load.get())
        else:
            # 如果没有区间，只绘制数据曲线
            self.ax_actual_load.clear()
            
            if self.actual_load_data:
                self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data, color='#2196F3', linewidth=1.8, alpha=0.9)
            
            if self.actual_load_data:
                self.set_xticks_for_line_numbers()
                tool_info = f"{prog_data['tool_id']} ({prog_data['start_line']}-{prog_data['end_line']})"
                self.ax_actual_load.set_title(f'{prog_data["name"]} - {tool_info} 数据预览')
                self.ax_actual_load.set_xlabel('程序行号位置')
                self.ax_actual_load.set_ylabel('数据值')
                self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
                
        self.canvas_actual_load.draw()
        self.original_xlim = self.ax_actual_load.get_xlim()
        self.original_ylim = self.ax_actual_load.get_ylim()
        
        self.status_var_actual_load.set(f"📍 已切换到 {prog_data['name']} - {prog_data['tool_id']}")
    
    def switch_to_program(self, program_id):
        """切换到指定程序的数据"""
        self.current_program_id = program_id
        prog_data = self.programs_data[program_id]
        
        self.actual_load_data = prog_data['data'] if isinstance(prog_data['data'], list) else prog_data['data'].tolist()
        self.actual_load_line_numbers = prog_data['line_numbers'] if isinstance(prog_data['line_numbers'], list) else prog_data['line_numbers'].tolist()
        self.actual_load_point_indices = prog_data['point_indices'] if isinstance(prog_data['point_indices'], list) else prog_data['point_indices'].tolist()
        self.actual_load_x_positions = prog_data['x_positions'] if isinstance(prog_data['x_positions'], list) else prog_data['x_positions'].tolist()
        self.actual_load_unique_line_numbers = prog_data['unique_line_numbers'] if isinstance(prog_data['unique_line_numbers'], list) else prog_data['unique_line_numbers'].tolist()
        self.actual_load_intervals = prog_data['intervals']
        self.actual_load_interval_values = prog_data['interval_values']
        self.filtered_data = prog_data['filtered_data']
        self.is_filtered = prog_data['is_filtered']
        self.current_intervals = prog_data['intervals']
        
        if 'adjustment_ratio' not in prog_data:
            prog_data['adjustment_ratio'] = 1.1
        self.current_adjustment_ratio = prog_data['adjustment_ratio']
        
        if hasattr(self, 'ratio_scale'):
            self.ratio_scale.set(self.current_adjustment_ratio)
        
        self.cutoff_freq.set(prog_data.get('cutoff_freq', 0.1))
        self.filter_order.set(prog_data.get('filter_order', 4))
        
        # 切换程序后：确保微调模式为关闭状态
        if hasattr(self, 'adjustment_mode'):
            self.adjustment_mode = False
        if hasattr(self, 'adjustment_button'):
            self.adjustment_button.config(text="✏️ 微调")
        
        # 显示区间平均值而非整体平均值
        interval_avg = self.calculate_interval_average(prog_data)
        self.average_value_label.config(text=f"{interval_avg:.3f}")
        
        self.update_ideal_value()
        
        self.ax_actual_load.clear()
        
        if self.actual_load_data:
            self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data, color='#2196F3', linewidth=1.8, alpha=0.9)
        
        if self.actual_load_data:
            self.set_xticks_for_line_numbers()
            self.ax_actual_load.set_title(f'{prog_data["name"]} 数据预览')
            self.ax_actual_load.set_xlabel('程序行号位置')
            self.ax_actual_load.set_ylabel('数据值')
            self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
            self.canvas_actual_load.draw()
            
            self.original_xlim = self.ax_actual_load.get_xlim()
            self.original_ylim = self.ax_actual_load.get_ylim()
            
            if not hasattr(self, 'scroll_cid') or self.scroll_cid is None:
                self.setup_chart_interactions()
        
        # 清空结果文本区域
        self.actual_load_result_text.delete(1.0, tk.END)
        
        # 根据当前刀具是否已划分来决定显示内容
        if self.actual_load_intervals and len(self.actual_load_intervals) > 0:
            # 当前刀具已划分，显示当前刀具的详细区间信息
            data_type = "滤波" if self.is_filtered else "原始"
            self.update_interval_display(data_type, self.reduce_interval_actual_load.get())
            self.plot_steady_intervals(data_type)
            
            if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
                self.draw_interval_boundaries()
            
            self.status_var_actual_load.set(f"已切换到程序: {prog_data['name']} (已加载 {len(self.actual_load_intervals)} 个稳态区间)")
        else:
            # 当前刀具未划分，显示所有已划分区间的汇总信息
            self.update_all_intervals_summary()
            self.status_var_actual_load.set(f"已切换到程序: {prog_data['name']} (数据点数: {len(self.actual_load_data)})")
    
    def refresh_display(self):
        """刷新显示：去掉滤波，重新显示原始数据和区间分割"""
        if not self.current_program_id or self.current_program_id not in self.programs_data:
            messagebox.showwarning("无数据", "请先选择程序")
            return
        
        # 清除滤波数据
        self.filtered_data = None
        self.is_filtered = False
        
        # 保存当前程序状态
        if self.current_program_id and self.current_program_id in self.programs_data:
            prog_data = self.programs_data[self.current_program_id]
            prog_data['filtered_data'] = None
            prog_data['is_filtered'] = False
        
        # 重新切换到当前程序（刷新显示）
        self.switch_to_program(self.current_program_id)
        
        self.status_var_actual_load.set("已刷新显示：使用原始数据")
    
    def calculate_interval_average(self, prog_data):
        """计算已划分区间数据的平均值
        
        Args:
            prog_data: 程序/刀具数据字典
            
        Returns:
            float: 区间数据的平均值，如果没有区间则返回整体平均值
        """
        intervals = prog_data.get('intervals', [])
        if not intervals:
            # 没有区间，返回整体平均值
            return prog_data.get('average', 0)
        
        # 获取数据（优先使用滤波数据）
        if prog_data.get('is_filtered') and prog_data.get('filtered_data') is not None:
            data = prog_data['filtered_data']
        else:
            data = prog_data['data']
        
        if data is None or len(data) == 0:
            return prog_data.get('average', 0)
        
        # 收集所有区间内的数据点
        interval_data_points = []
        for start_idx, end_idx in intervals:
            if 0 <= start_idx < len(data) and 0 <= end_idx < len(data):
                interval_data_points.extend(data[start_idx:end_idx+1])
        
        # 计算区间数据的平均值
        if interval_data_points:
            return float(np.mean(interval_data_points))
        else:
            return prog_data.get('average', 0)
    
    def update_ideal_value(self, sync_scale=True):
        """更新理想值显示
        
        Args:
            sync_scale: 是否同步更新滑块位置，默认True
        """
        if not self.current_program_id or self.current_program_id not in self.programs_data:
            return
        
        # 获取当前刀具的数据（新版本支持刀具）
        if hasattr(self, 'current_tool_key') and self.current_tool_key:
            # 新版本：从刀具级别获取数据
            if self.current_tool_key not in self.programs_data[self.current_program_id]:
                return
            prog_data = self.programs_data[self.current_program_id][self.current_tool_key]
        else:
            # 旧版本：从程序级别获取数据
            prog_data = self.programs_data[self.current_program_id]
        
        if 'average' in prog_data:
            try:
                # 从输入框获取修调倍率
                if hasattr(self, 'adjustment_ratio_entry'):
                    ratio_text = self.adjustment_ratio_entry.get()
                    ratio = float(ratio_text) if ratio_text else self.current_adjustment_ratio
                    # 保存到当前刀具的数据中
                    prog_data['adjustment_ratio'] = ratio
                    self.current_adjustment_ratio = ratio
                    # 同步更新滑块的值（仅在从文本框触发时）
                    if sync_scale and hasattr(self, 'ratio_scale'):
                        self.ratio_scale.set(ratio)
                else:
                    ratio = self.current_adjustment_ratio
                
                # 使用区间平均值的平均值计算理想值（与保存逻辑一致）
                base_value = self.calculate_interval_average(prog_data)
                ideal_value = base_value * ratio
                self.ideal_value_label.config(text=f"{ideal_value:.3f}")
            except (tk.TclError, ValueError):
                # 如果输入无效,显示错误
                self.ideal_value_label.config(text="无效输入")
    
    def save_current_program_state(self):
        """保存当前程序和刀具的状态"""
        if not hasattr(self, 'current_tool_key') or not self.current_tool_key:
            # 兼容旧版本：如果没有刀具key，尝试保存程序级别数据
            if self.current_program_id and self.current_program_id in self.programs_data:
                prog_data = self.programs_data[self.current_program_id]
                if not isinstance(prog_data, dict) or 'data' in prog_data:
                    # 旧格式数据
                    prog_data['data'] = np.array(self.actual_load_data) if isinstance(self.actual_load_data, list) else self.actual_load_data
                    prog_data['intervals'] = self.actual_load_intervals
                    prog_data['interval_values'] = self.actual_load_interval_values
            return
        
        # 新版本：保存刀具级别数据
        if self.current_program_id and self.current_tool_key:
            if self.current_program_id in self.programs_data:
                if self.current_tool_key in self.programs_data[self.current_program_id]:
                    prog_data = self.programs_data[self.current_program_id][self.current_tool_key]
                    
                    # 根据当前数据源更新对应的数据
                    data_source = self.data_source.get()
                    if data_source == '电流':
                        prog_data['current_data'] = np.array(self.actual_load_data) if isinstance(self.actual_load_data, list) else self.actual_load_data
                    elif data_source == 'vgpro功率':
                        prog_data['vgpro_power_data'] = np.array(self.actual_load_data) if isinstance(self.actual_load_data, list) else self.actual_load_data
                    elif data_source == '边缘模块功率':
                        prog_data['edge_power_data'] = np.array(self.actual_load_data) if isinstance(self.actual_load_data, list) else self.actual_load_data
                    
                    prog_data['data'] = np.array(self.actual_load_data) if isinstance(self.actual_load_data, list) else self.actual_load_data
                    prog_data['line_numbers'] = np.array(self.actual_load_line_numbers) if isinstance(self.actual_load_line_numbers, list) else self.actual_load_line_numbers
                    prog_data['point_indices'] = np.array(self.actual_load_point_indices) if isinstance(self.actual_load_point_indices, list) else self.actual_load_point_indices
                    prog_data['x_positions'] = np.array(self.actual_load_x_positions) if isinstance(self.actual_load_x_positions, list) else self.actual_load_x_positions
                    prog_data['unique_line_numbers'] = np.array(self.actual_load_unique_line_numbers) if isinstance(self.actual_load_unique_line_numbers, list) else self.actual_load_unique_line_numbers
                    prog_data['intervals'] = self.actual_load_intervals
                    prog_data['interval_values'] = self.actual_load_interval_values
                    prog_data['filtered_data'] = self.filtered_data
                    prog_data['is_filtered'] = self.is_filtered
                    prog_data['overall_reduce_interval'] = self.reduce_interval_actual_load.get()
                    prog_data['cutoff_freq'] = self.cutoff_freq.get()
                    prog_data['filter_order'] = self.filter_order.get()
    
    def create_interface(self):
        """创建界面 - 集成式单页面布局"""
        # 设置主窗口背景色为清新浅色风格
        self.root.configure(bg='#f0f4f8')
        
        # 配置现代化样式
        style = ttk.Style()
        style.theme_use('clam')  # 使用clam主题作为基础
        
        # 配置颜色方案 - 清新浅色主题，蓝色数据线醒目
        bg_light = '#f0f4f8'       # 浅灰蓝色背景
        bg_card = '#ffffff'        # 纯白卡片背景
        accent_blue = '#1e88e5'    # 鲜艳蓝色强调
        accent_orange = '#ff6b35'  # 橙色高亮按钮
        text_dark = '#2c3e50'      # 深色文字
        text_gray = '#546e7a'      # 灰色次要文字
        
        # 配置Frame样式
        style.configure('Main.TFrame', background=bg_light)
        style.configure('Card.TFrame', background=bg_card, relief='flat', borderwidth=0)
        
        # 配置LabelFrame样式 - 清新边框
        style.configure('TLabelframe', 
                       background=bg_card, 
                       bordercolor='#90caf9',
                       borderwidth=2,
                       relief='groove')
        style.configure('TLabelframe.Label', 
                       background=bg_card,
                       foreground=text_dark,
                       font=('Microsoft YaHei', 11, 'bold'))
        
        # 配置Button样式 - 清新风格
        style.configure('TButton',
                       background='#64b5f6',
                       foreground='#ffffff',
                       borderwidth=0,
                       font=('Microsoft YaHei', 10),
                       padding=(10, 5))
        style.map('TButton',
                 background=[('active', '#42a5f5'), ('pressed', '#1e88e5')],
                 foreground=[('active', '#ffffff')])
        
        style.configure('Action.TButton',
                       background=accent_orange,
                       foreground='#ffffff',
                       font=('Microsoft YaHei', 10, 'bold'),
                       padding=(12, 6))
        style.map('Action.TButton',
                 background=[('active', '#ff8a65'), ('pressed', '#f4511e')],
                 foreground=[('active', '#ffffff')])
        
        # 配置Label样式
        style.configure('TLabel',
                       background=bg_card,
                       foreground=text_dark,
                       font=('Microsoft YaHei', 10))
        style.configure('Title.TLabel',
                       background=bg_card,
                       foreground=text_dark,
                       font=('Microsoft YaHei', 12, 'bold'))
        style.configure('Value.TLabel',
                       background=bg_card,
                       foreground=accent_blue,
                       font=('Microsoft YaHei', 11, 'bold'))
        
        # 配置Combobox样式
        style.configure('TCombobox',
                       fieldbackground='#ffffff',
                       background='#64b5f6',
                       foreground=text_dark,
                       arrowcolor='#ffffff',
                       borderwidth=1,
                       relief='flat')
        style.map('TCombobox',
                 fieldbackground=[('readonly', '#ffffff')],
                 selectbackground=[('readonly', '#90caf9')],
                 selectforeground=[('readonly', text_dark)])
        
        # 配置Entry样式
        style.configure('TEntry',
                       fieldbackground='#ffffff',
                       foreground=text_dark,
                       insertcolor=accent_blue,
                       borderwidth=1,
                       relief='flat')
        
        # 配置Scale样式
        style.configure('Horizontal.TScale',
                       background=bg_card,
                       troughcolor='#e3f2fd',
                       borderwidth=0,
                       sliderlength=20,
                       sliderrelief='flat')
        
        # 主框架 - 应用深色背景
        main_frame = ttk.Frame(self.root, padding="15", style='Main.TFrame')
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 顶部：当前程序选择和数据源选择 - 科技感卡片
        top_frame = ttk.LabelFrame(main_frame, text="📊 当前程序", padding="10", style='TLabelframe')
        top_frame.pack(fill=tk.X, pady=(0, 8), padx=2)
        
        program_row = ttk.Frame(top_frame, style='Card.TFrame')
        program_row.pack(fill=tk.X)
        
        # 程序选择
        ttk.Label(program_row, text="程序名:", style='TLabel').pack(side=tk.LEFT, padx=(5, 8))
        self.program_selector = ttk.Combobox(program_row, state="readonly", width=35, style='TCombobox')
        self.program_selector.pack(side=tk.LEFT, padx=3)
        self.program_selector.bind("<<ComboboxSelected>>", self.on_program_selected)
        
        # 刀具选择
        ttk.Label(program_row, text="刀具号:", style='TLabel').pack(side=tk.LEFT, padx=(20, 8))
        self.tool_selector = ttk.Combobox(program_row, state="readonly", width=20, style='TCombobox')
        self.tool_selector.pack(side=tk.LEFT, padx=3)
        self.tool_selector.bind("<<ComboboxSelected>>", self.on_tool_selected)
        
        # 数据源选择
        ttk.Label(program_row, text="数据源:", style='TLabel').pack(side=tk.LEFT, padx=(20, 8))
        data_source_menu = ttk.Combobox(program_row, textvariable=self.data_source, 
                                       values=['电流', 'vgpro功率', '边缘模块功率'], 
                                       state="readonly", width=12, style='TCombobox')
        data_source_menu.pack(side=tk.LEFT, padx=3)
        data_source_menu.bind("<<ComboboxSelected>>", self.on_data_source_changed)
        
        # 功率信息行（紧凑布局）- 科技感设计
        power_info_frame = ttk.Frame(main_frame, style='Card.TFrame', padding="8")
        power_info_frame.pack(fill=tk.X, pady=(0, 8), padx=2)
        
        # 配置浅色Entry样式
        power_entry_style = {'background': '#ffffff', 'foreground': '#2c3e50', 
                            'insertbackground': '#1e88e5', 'relief': 'solid',
                            'font': ('Microsoft YaHei', 11), 'borderwidth': 1}
        
        # 基准值 - 发光效果
        ttk.Label(power_info_frame, text="⚡ 基准值:", style='TLabel').pack(side=tk.LEFT, padx=(5, 8))
        self.average_value_label = ttk.Label(power_info_frame, text="0.537", style='Value.TLabel')
        self.average_value_label.pack(side=tk.LEFT, padx=3)
        
        # 优化倍率
        ttk.Label(power_info_frame, text="🎯 优化倍率:", style='TLabel').pack(side=tk.LEFT, padx=(20, 8))
        # 使用tk.Entry以便自定义颜色
        self.adjustment_ratio_entry = tk.Entry(power_info_frame, width=8, **power_entry_style)
        self.adjustment_ratio_entry.pack(side=tk.LEFT, padx=2)
        self.adjustment_ratio_entry.insert(0, "1.2")
        self.adjustment_ratio_entry.bind('<Return>', lambda e: self.update_ideal_value())
        
        # 滑块 - 深蓝色配色，更清晰可见
        self.ratio_scale = tk.Scale(power_info_frame, from_=1.0, to=2.0, orient=tk.HORIZONTAL, length=150,
                                    resolution=0.01, showvalue=False, command=self.on_ratio_scale_changed,
                                    bg='#ffffff', troughcolor='#bbdefb', activebackground='#1565c0',
                                    highlightthickness=1, highlightbackground='#90caf9', sliderlength=30, sliderrelief='raised',
                                    fg='#2c3e50', font=('Microsoft YaHei', 9))
        self.ratio_scale.pack(side=tk.LEFT, padx=5)
        self.ratio_scale.set(1.2)
        
        # 理想功率 - 高亮显示
        ttk.Label(power_info_frame, text="✨ 理想功率:", style='TLabel').pack(side=tk.LEFT, padx=(20, 8))
        self.ideal_value_label = ttk.Label(power_info_frame, text="1.234", style='Value.TLabel')
        self.ideal_value_label.pack(side=tk.LEFT, padx=3)
        
        # 创建一个横向容器，用于并列放置"区间划分"和"稳态区间详情"
        analysis_container = ttk.Frame(main_frame, style='Main.TFrame')
        analysis_container.pack(fill=tk.X, pady=(0, 8))
        
        # 区间划分参数框 - 更紧凑的布局（左侧）- 科技感卡片
        division_frame = ttk.LabelFrame(analysis_container, text="🔬 区间分析", padding="10", style='TLabelframe')
        division_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(2, 5))
        
        # 第一行：操作按钮
        row1_frame = ttk.Frame(division_frame, style='Card.TFrame')
        row1_frame.pack(fill=tk.X, pady=3)
        
        # 第二行：灵敏度控制和操作按钮
        row2_frame = ttk.Frame(division_frame, style='Card.TFrame')
        row2_frame.pack(fill=tk.X, pady=3)
        
        # 灵敏度滑块 - 深蓝色配色，更清晰可见（范围扩大以支持更粗/更细的控制）
        ttk.Label(row2_frame, text="🎚️ 灵敏度:", style='TLabel').pack(side=tk.LEFT, padx=(5, 8))
        sensitivity_scale = tk.Scale(row2_frame, from_=0.2, to=5.0, orient=tk.HORIZONTAL, length=260,
                        resolution=0.1, variable=self.auto_sensitivity, showvalue=True,
                        bg='#ffffff', troughcolor='#bbdefb', activebackground='#1565c0',
                        highlightthickness=1, highlightbackground='#90caf9', sliderlength=30, sliderrelief='raised',
                        fg='#2c3e50', font=('Microsoft YaHei', 9))
        sensitivity_scale.pack(side=tk.LEFT, padx=3)
        ttk.Label(row2_frame, text="(越大越灵敏)", style='TLabel', font=('Microsoft YaHei', 9)).pack(side=tk.LEFT, padx=5)
        
        # 自动划分按钮 - 强调色
        auto_analyze_btn = ttk.Button(row2_frame, text="🚀 自动划分", command=self.analyze_auto, 
                  width=12, style='Action.TButton')
        auto_analyze_btn.pack(side=tk.LEFT, padx=15, ipady=4)
        
        # 批量划分按钮 - 强调色
        batch_analyze_btn = ttk.Button(row2_frame, text="📦 批量划分", command=self.show_batch_analyze_dialog, 
                  width=12, style='Action.TButton')
        batch_analyze_btn.pack(side=tk.LEFT, padx=3, ipady=4)
        
        # 保存按钮 - 强调色
        save_btn = ttk.Button(row2_frame, text="💾 保存", command=self.save_actual_load_results, 
                  width=10, style='Action.TButton')
        save_btn.pack(side=tk.LEFT, padx=3, ipady=4)
        # 保存按钮问号说明 - 小图标按钮
        save_help_btn = ttk.Button(row2_frame, text="❓", width=3, command=self.show_save_help, style='TButton')
        save_help_btn.pack(side=tk.LEFT, padx=2)
        
        # 稳态区间详情框（右侧，与区间分析并列）- 科技感卡片
        detail_frame = ttk.LabelFrame(analysis_container, text="📋 稳态区间详情", padding="10", style='TLabelframe')
        detail_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 2))
        
        # 创建文本区域显示结果 - 浅色主题
        self.actual_load_result_text = tk.Text(detail_frame, height=6, wrap=tk.WORD, 
                                              font=('Consolas', 10),
                                              bg='#fafafa', fg='#2c3e50',
                                              insertbackground='#1e88e5',
                                              selectbackground='#bbdefb',
                                              selectforeground='#2c3e50',
                                              relief='solid', borderwidth=1)
        self.actual_load_result_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=3, pady=3)
        
        # 滚动条 - 浅色样式
        scrollbar_style = ttk.Style()
        scrollbar_style.configure('Light.Vertical.TScrollbar',
                                 background='#e3f2fd',
                                 troughcolor='#ffffff',
                                 borderwidth=0,
                                 arrowcolor='#64b5f6')
        scrollbar = ttk.Scrollbar(detail_frame, orient=tk.VERTICAL, 
                                command=self.actual_load_result_text.yview,
                                style='Light.Vertical.TScrollbar')
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y, pady=3)
        self.actual_load_result_text.config(yscrollcommand=scrollbar.set)
        
        # 图表区域 - 深色背景卡片
        self.actual_load_figure_frame = ttk.Frame(main_frame, style='Card.TFrame', padding="5")
        self.actual_load_figure_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 8), padx=2)
        
        # 状态栏 - 清新设计
        self.status_var_actual_load = tk.StringVar()
        self.status_var_actual_load.set("⚡ 系统就绪")
        status_bar = tk.Label(self.root, 
                            textvariable=self.status_var_actual_load,
                            bg='#e3f2fd', fg='#2c3e50',
                            font=('Microsoft YaHei', 9),
                            anchor=tk.W, padx=15, pady=5,
                            relief='flat')
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 初始提示
        self.show_actual_load_initial_message()
    
    def show_save_help(self):
        help_text = """保存逻辑说明：

1. 整体模式：保存当前程序的所有稳态区间分析结果

2. 分段模式：
   - 保存所有分段的稳态区间分析结果
   - 自动合并相邻分段之间的连续区间
   - 避免在分段边界产生不必要的断裂

3. 保存内容：
   - 区间起止位置（行号.点索引格式）
   - 区间长度和统计信息
   - 理想功率值
   - 详细分析报告

4. 保存格式：生成 .txt 格式的详细报告文件

💡 提示：自动划分后，可在图表上直观查看结果
如需微调，可调整灵敏度后重新分析，或使用微调功能"""
        messagebox.showinfo("保存逻辑说明", help_text)
    
    def show_batch_analyze_dialog(self):
        """显示批量自动划分对话框"""
        if not self.program_mapping:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        # 创建对话框
        dialog = tk.Toplevel(self.root)
        dialog.title("批量自动划分")
        dialog.geometry("600x500")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # 居中显示
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() // 2) - 300
        y = (dialog.winfo_screenheight() // 2) - 250
        dialog.geometry(f"600x500+{x}+{y}")
        
        # 顶部说明
        info_frame = ttk.Frame(dialog, padding="10")
        info_frame.pack(fill=tk.X)
        ttk.Label(info_frame, text="请勾选需要批量自动划分的刀具：", 
                 font=('Microsoft YaHei', 11, 'bold')).pack(anchor=tk.W)
        
        # 创建树形视图框架
        tree_frame = ttk.Frame(dialog)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 创建Treeview和滚动条
        tree = ttk.Treeview(tree_frame, columns=('status',), show='tree headings', selectmode='none')
        tree.heading('#0', text='程序 / 刀具')
        tree.heading('status', text='状态')
        tree.column('#0', width=400)
        tree.column('status', width=150, anchor='center')
        
        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 存储复选框状态的字典 {(program_id, tool_id): BooleanVar}
        checkboxes = {}
        
        # 填充树形视图
        for program_id, program_info in sorted(self.program_mapping.items()):
            program_name = program_info['name']
            tools_list = program_info.get('tools_list', [])
            
            # 添加程序节点
            program_node = tree.insert('', 'end', text=f"📁 {program_name} ({program_id})", 
                                      values=('',), tags=('program',))
            
            # 按txt文件顺序遍历刀具(使用索引)
            for idx, tool_info in enumerate(tools_list):
                tool_id = tool_info['tool_id']
                start = tool_info['start']
                end = tool_info['end']
                tool_key = f"{tool_id}_{idx}"
                
                # 检查是否已经划分
                has_intervals = False
                if program_id in self.programs_data:
                    if tool_key in self.programs_data[program_id]:
                        tool_data = self.programs_data[program_id][tool_key]
                        if 'intervals' in tool_data and tool_data['intervals']:
                            has_intervals = True
                
                status = "✓ 已划分" if has_intervals else ""
                tool_node = tree.insert(program_node, 'end', 
                                       text=f"🔧 {tool_id} ({start}-{end})",
                                       values=(status,), 
                                       tags=('tool',))
                
                # 为每个刀具创建一个选择变量(key: (program_id, tool_key))
                var = tk.BooleanVar(value=False)
                checkboxes[(program_id, tool_key)] = var
        
        # 绑定点击事件（切换复选状态）
        def on_tree_click(event):
            item = tree.identify('row', event.x, event.y)
            if item and 'tool' in tree.item(item, 'tags'):
                # 获取对应的程序ID和刀具key
                parent = tree.parent(item)
                parent_text = tree.item(parent, 'text')
                tool_text = tree.item(item, 'text')
                
                # 移除可能的复选标记再解析
                tool_text_clean = tool_text.replace('☑ ', '')
                
                # 解析程序ID
                import re
                prog_match = re.search(r'\(([^)]+)\)$', parent_text)
                tool_match = re.match(r'🔧 ([^\s]+)', tool_text_clean)
                
                if prog_match and tool_match:
                    program_id = prog_match.group(1)
                    tool_id = tool_match.group(1)
                    
                    # 获取刀具在树中的索引
                    parent_children = tree.get_children(parent)
                    tool_index = list(parent_children).index(item)
                    tool_key = f"{tool_id}_{tool_index}"
                    
                    if (program_id, tool_key) in checkboxes:
                        # 切换选择状态
                        var = checkboxes[(program_id, tool_key)]
                        var.set(not var.get())
                        
                        # 更新显示（在文本前添加复选标记）
                        current_text = tree.item(item, 'text')
                        if var.get():
                            if not current_text.startswith('☑'):
                                new_text = '☑ ' + current_text
                                tree.item(item, text=new_text)
                        else:
                            if current_text.startswith('☑'):
                                new_text = current_text[2:]  # 移除"☑ "
                                tree.item(item, text=new_text)
        
        tree.bind('<Button-1>', on_tree_click)
        
        # 底部按钮
        button_frame = ttk.Frame(dialog, padding="10")
        button_frame.pack(fill=tk.X)
        
        # 全选/取消全选
        def toggle_all():
            all_selected = all(var.get() for var in checkboxes.values())
            new_state = not all_selected
            
            for var in checkboxes.values():
                var.set(new_state)
            
            # 更新树形视图显示
            for item in tree.get_children():
                for child in tree.get_children(item):
                    current_text = tree.item(child, 'text')
                    if new_state:
                        if not current_text.startswith('☑'):
                            tree.item(child, text='☑ ' + current_text)
                    else:
                        if current_text.startswith('☑'):
                            tree.item(child, text=current_text[2:])
        
        ttk.Button(button_frame, text="全选/取消", command=toggle_all, width=12).pack(side=tk.LEFT, padx=5)
        
        # 开始批量划分按钮
        def start_batch_analyze():
            # 收集选中的刀具 (program_id, tool_key)
            selected = [(pid, tkey) for (pid, tkey), var in checkboxes.items() if var.get()]
            
            if not selected:
                messagebox.showwarning("未选择", "请至少选择一个刀具进行划分")
                return
            
            dialog.destroy()
            
            # 执行批量划分
            self.execute_batch_analyze(selected)
        
        ttk.Button(button_frame, text="开始批量划分", command=start_batch_analyze, 
                  width=15, style='Action.TButton').pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="取消", command=dialog.destroy, 
                  width=10).pack(side=tk.RIGHT, padx=5)
    
    def execute_batch_analyze(self, selected_tools):
        """执行批量自动划分
        
        Args:
            selected_tools: List[(program_id, tool_key)]
        """
        # 保存当前程序和刀具
        saved_program_id = self.current_program_id
        saved_tool_key = self.current_tool_key
        
        # 创建进度窗口
        progress_window = tk.Toplevel(self.root)
        progress_window.title("批量自动划分")
        progress_window.geometry("500x200")
        progress_window.transient(self.root)
        progress_window.grab_set()
        
        # 居中显示
        progress_window.update_idletasks()
        x = (progress_window.winfo_screenwidth() // 2) - 250
        y = (progress_window.winfo_screenheight() // 2) - 100
        progress_window.geometry(f"500x200+{x}+{y}")
        
        # 进度信息
        info_frame = ttk.Frame(progress_window, padding="20")
        info_frame.pack(fill=tk.BOTH, expand=True)
        
        status_label = tk.Label(info_frame, text=f"正在批量划分，共 {len(selected_tools)} 个刀具...", 
                               font=('Microsoft YaHei', 11))
        status_label.pack(pady=10)
        
        progress_bar = ttk.Progressbar(info_frame, mode='determinate', length=400, maximum=len(selected_tools))
        progress_bar.pack(pady=10)
        
        detail_label = tk.Label(info_frame, text="", font=('Microsoft YaHei', 9), fg='gray')
        detail_label.pack(pady=5)
        
        # 统计信息
        success_count = 0
        fail_count = 0
        fail_list = []
        
        # 逐个处理
        for idx, (program_id, tool_key) in enumerate(selected_tools):
            try:
                # 更新显示
                program_name = self.program_mapping[program_id]['name']
                # 从tool_key中提取tool_id用于显示
                tool_id_display = tool_key.rsplit('_', 1)[0] if '_' in tool_key else tool_key
                detail_label.config(text=f"正在处理: {program_name} - {tool_id_display} ({idx+1}/{len(selected_tools)})")
                progress_window.update()
                
                # 切换到该刀具
                self.current_program_id = program_id
                self.current_tool_key = tool_key
                
                # 加载数据
                prog_data = self.programs_data[program_id][tool_key]
                self.actual_load_data = prog_data['data'] if isinstance(prog_data['data'], list) else prog_data['data'].tolist()
                self.actual_load_line_numbers = prog_data['line_numbers'] if isinstance(prog_data['line_numbers'], list) else prog_data['line_numbers'].tolist()
                self.actual_load_point_indices = prog_data['point_indices'] if isinstance(prog_data['point_indices'], list) else prog_data['point_indices'].tolist()
                self.actual_load_x_positions = prog_data['x_positions'] if isinstance(prog_data['x_positions'], list) else prog_data['x_positions'].tolist()
                self.actual_load_unique_line_numbers = prog_data['unique_line_numbers'] if isinstance(prog_data['unique_line_numbers'], list) else prog_data['unique_line_numbers'].tolist()
                self.filtered_data = prog_data.get('filtered_data')
                self.is_filtered = prog_data.get('is_filtered', False)
                
                # 确定使用原始数据还是滤波数据
                if self.is_filtered and self.filtered_data is not None:
                    analysis_data = self.filtered_data
                else:
                    analysis_data = self.actual_load_data
                
                # 自动标定参数
                params = self.auto_calibrate_params(analysis_data)
                
                # 生成候选区间
                ivs = self.propose_intervals_auto(
                    analysis_data,
                    params['abs_thr'],
                    params['rel_thr'],
                    params['min_len'],
                    params['slope_thr']
                )
                
                # 如果没有找到区间，尝试降低灵敏度再试一次
                if not ivs:
                    original_sensitivity = self.auto_sensitivity.get()
                    self.auto_sensitivity.set(original_sensitivity * 0.8)
                    params = self.auto_calibrate_params(analysis_data)
                    ivs = self.propose_intervals_auto(
                        analysis_data,
                        params['abs_thr'],
                        params['rel_thr'],
                        params['min_len'],
                        params['slope_thr']
                    )
                    self.auto_sensitivity.set(original_sensitivity)
                
                if ivs:
                    # 保存区间结果
                    prog_data['intervals'] = ivs
                    prog_data['interval_values'] = []
                    
                    # 计算区间均值
                    for start_idx, end_idx in ivs:
                        if start_idx < len(analysis_data) and end_idx < len(analysis_data):
                            interval_data = analysis_data[start_idx:end_idx+1]
                            interval_avg = np.mean(interval_data)
                            prog_data['interval_values'].append(interval_avg)
                    
                    success_count += 1
                else:
                    fail_count += 1
                    fail_list.append(f"{program_name} - {tool_id_display}")
                
            except Exception as e:
                fail_count += 1
                fail_list.append(f"{program_name} - {tool_id_display} (错误: {str(e)})")
            
            # 更新进度条
            progress_bar['value'] = idx + 1
            progress_window.update()
        
        # 恢复原来的程序和刀具
        if saved_program_id and saved_tool_key:
            self.current_program_id = saved_program_id
            self.current_tool_key = saved_tool_key
            # 重新加载界面
            if saved_program_id in self.programs_data and saved_tool_key in self.programs_data[saved_program_id]:
                prog_data = self.programs_data[saved_program_id][saved_tool_key]
                self.load_program_data_to_ui(prog_data)
        
        # 关闭进度窗口
        progress_window.destroy()
        
        # 更新所有刀具选择器的显示（显示✓标记）
        for program_id in self.program_mapping.keys():
            self.update_tool_selector(program_id, preserve_selection=True)
        
        # 显示结果
        result_msg = f"✓ 批量自动划分完成！\n\n"
        result_msg += f"成功: {success_count} 个刀具\n"
        if fail_count > 0:
            result_msg += f"失败: {fail_count} 个刀具\n\n"
            result_msg += "失败的刀具：\n"
            for fail_item in fail_list[:10]:  # 最多显示10个
                result_msg += f"  • {fail_item}\n"
            if len(fail_list) > 10:
                result_msg += f"  ... 还有 {len(fail_list) - 10} 个\n"
        
        messagebox.showinfo("批量划分完成", result_msg)
        self.status_var_actual_load.set(f"✓ 批量划分完成：成功 {success_count} 个，失败 {fail_count} 个")
        
        # 刷新稳态区间汇总显示
        self.update_all_intervals_summary()
    
    def show_adjustment_help(self):
        """显示微调功能帮助"""
        help_text = """微调功能使用说明：

【启用微调模式】
1. 先进行"自动划分"得到初始区间
2. 点击图表上方的 "✏️ 微调" 按钮进入微调模式
3. 进入后会显示红色（起始）和蓝色（结束）边界线

【调整区间边界】
• 鼠标悬停在边界线上（红色或蓝色），光标会变化
• 按住左键拖动边界线到新位置
• 释放鼠标确认调整
• 起始边界不能超过结束边界
• 调整后图表和高亮区域会立即更新
• ⭐ 如果边界重合或跨越，相邻区间会自动合并

【添加新区间】
• 点击图表上方的 "➕ 添加" 按钮进入添加模式
• 在图表上点击选择起始位置（显示橙色虚线标记）
• 再次点击选择结束位置
• 系统会自动检查是否与现有区间重叠
• 添加后会自动按位置排序并刷新显示
• 右键点击可取消添加操作

【删除区间】
• 在微调模式下，右键点击要删除的区间内任意位置
• 弹出确认对话框，点击"是"确认删除
• 删除后图表会自动刷新，移除该区间

【手动合并区间】
• 按住 Ctrl 键，依次左键点击要合并的多个区间
• 选中的区间会以黄色高亮显示
• 点击"合并区间"按钮完成合并
• 选择不连续区间时会合并中间所有区间
• 合并后会自动刷新显示

【退出微调模式】
再次点击 "✓ 微调中" 按钮退出微调模式

【注意事项】
✓ 每个程序的区间独立管理
✓ 切换程序会自动保存当前程序的区间
✓ 微调完成后记得点击"保存"按钮
✓ 微调模式下可以使用鼠标滚轮缩放图表，方便精确调整
✓ 微调模式下平移功能被禁用，避免误操作"""
        messagebox.showinfo("微调功能说明", help_text)
    
    def on_ratio_scale_changed(self, value):
        """优化倍率滑块变化回调"""
        try:
            ratio_value = float(value)
            # 更新文本框显示
            self.adjustment_ratio_entry.delete(0, tk.END)
            self.adjustment_ratio_entry.insert(0, f"{ratio_value:.3f}")
            
            # 直接保存倍率并更新理想功率
            if not self.current_program_id or self.current_program_id not in self.programs_data:
                return
            
            # 获取当前刀具的数据（新版本支持刀具）
            if hasattr(self, 'current_tool_key') and self.current_tool_key:
                # 新版本：从刀具级别获取数据
                if self.current_tool_key not in self.programs_data[self.current_program_id]:
                    return
                prog_data = self.programs_data[self.current_program_id][self.current_tool_key]
            else:
                # 旧版本：从程序级别获取数据
                prog_data = self.programs_data[self.current_program_id]
            
            prog_data['adjustment_ratio'] = ratio_value
            self.current_adjustment_ratio = ratio_value
            
            # 同时保存灵敏度到当前刀具
            if hasattr(self, 'auto_sensitivity'):
                prog_data['auto_sensitivity'] = self.auto_sensitivity.get()
            
            # 计算并更新理想功率（使用区间平均值的平均值）
            if 'average' in prog_data:
                base_value = self.calculate_interval_average(prog_data)
                ideal_value = base_value * ratio_value
                self.ideal_value_label.config(text=f"{ideal_value:.3f}")
        except:
            pass
    
    # 已移除波动阈值滑块回调（基于输入参数）
    
    # 已删除基于输入参数的分析方法
    
    def refresh_plot(self):
        """刷新图表 - 清除所有划分结果和分割点，只保留原始数据曲线"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showinfo("提示", "没有数据可刷新")
            return
        
        # 确认刷新
        result = messagebox.askyesno("确认刷新", "刷新将清除所有分割点和分析结果，只保留原始数据曲线，是否继续？")
        if not result:
            return
        
        # 清除划分结果（稳态区间）
        self.actual_load_intervals = []
        self.actual_load_interval_values = []
        self.current_intervals = []
        
        # 清除滤波数据，恢复原始数据
        self.filtered_data = None
        self.is_filtered = False
        
        # 清除微调相关状态
        if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
            # 如果处于微调模式，先退出
            self.adjustment_mode = False
            self.adjustment_button.config(text="✏️ 微调")
            self.disable_adjustment_mode()
        self.selected_intervals = []
        self.dragging_boundary = None
        self.clear_interval_boundaries()
        
        # 同步更新到当前程序的保存数据中（这是关键）
        # 创建全新的空列表，避免任何引用问题
        if self.current_program_id and self.current_program_id in self.programs_data:
            prog_data = self.programs_data[self.current_program_id]
            prog_data['segment_points'] = []
            prog_data['segment_lines'] = []
            prog_data['segment_texts'] = []
            prog_data['segments'] = []
            prog_data['segment_params'] = {}
            prog_data['intervals'] = []
            prog_data['interval_values'] = []
            prog_data['filtered_data'] = None
            prog_data['is_filtered'] = False
            # 确保更新所有相关引用
            prog_data['selected_segment_point_index'] = None
            # 清除分段模式状态
            prog_data['segment_mode'] = False
        
        # 更新UI组件（如果存在）
        # 清空结果文本框，显示数据基本信息
        if hasattr(self, 'actual_load_result_text'):
            self.actual_load_result_text.delete('1.0', tk.END)
            result_info = "已刷新图表，已清除所有分析结果\n\n"
            result_info += f"数据点数: {len(self.actual_load_data)}\n"
            if self.actual_load_data:
                result_info += f"数据范围: {min(self.actual_load_data):.3f} - {max(self.actual_load_data):.3f}\n"
            if hasattr(self, 'actual_load_line_numbers') and self.actual_load_line_numbers:
                result_info += f"程序行号范围: {min(self.actual_load_line_numbers):.0f} - {max(self.actual_load_line_numbers):.0f}\n"
            result_info += "\n请重新进行划分分析\n"
            self.actual_load_result_text.insert('1.0', result_info)
        
        # 强制清空matplotlib图表上的所有艺术家对象
        self.ax_actual_load.clear()
        
        # 确保区间列表确实为空（双重保险）
        self.current_intervals = []
        if self.current_program_id and self.current_program_id in self.programs_data:
            self.programs_data[self.current_program_id]['intervals'] = []
        
        # 重新绘制原始数据
        self.plot_actual_load_data()
        
        self.status_var_actual_load.set("✓ 已刷新：清除所有分割点和分析结果，显示原始数据")

    def bind_mousewheel_events(self, canvas):
        """绑定鼠标滚轮事件"""
        def _on_mousewheel(event):
            try:
                if hasattr(event, 'delta') and event.delta:
                    canvas.yview_scroll(int(-1*(event.delta/120)), "units")
                elif hasattr(event, 'num'):
                    if event.num == 4:
                        canvas.yview_scroll(-1, "units")
                    elif event.num == 5:
                        canvas.yview_scroll(1, "units")
            except:
                pass
        
        def _on_shift_mousewheel(event):
            try:
                if hasattr(event, 'delta') and event.delta:
                    canvas.xview_scroll(int(-1*(event.delta/120)), "units")
                elif hasattr(event, 'num'):
                    if event.num == 4:
                        canvas.xview_scroll(-1, "units")
                    elif event.num == 5:
                        canvas.xview_scroll(1, "units")
            except:
                pass
        
        # 绑定滚轮事件
        canvas.bind("<MouseWheel>", _on_mousewheel)
        canvas.bind("<Shift-MouseWheel>", _on_shift_mousewheel)
        canvas.bind("<Button-4>", _on_mousewheel)
        canvas.bind("<Button-5>", _on_mousewheel)
        canvas.bind("<Shift-Button-4>", _on_shift_mousewheel)
        canvas.bind("<Shift-Button-5>", _on_shift_mousewheel)

    def init_figure(self):
        """初始化图表 - 清新浅色主题"""
        # 设置matplotlib默认样式
        plt.style.use('default')
        
        # 确保中文字体正确显示
        plt.rcParams['font.sans-serif'] = ['SimHei', 'Microsoft YaHei', 'Arial Unicode MS']
        plt.rcParams['axes.unicode_minus'] = False
        
        # 初始化图表，设置合适的尺寸（宽度自适应，高度固定为5英寸）
        self.fig_actual_load = plt.figure(figsize=(10, 5), tight_layout=False, facecolor='#ffffff')
        
        # 调整子图边距
        self.fig_actual_load.subplots_adjust(
            left=0.06,
            bottom=0.08,
            right=0.98,
            top=0.96,
            wspace=0.1,
            hspace=0.1
        )
        
        self.ax_actual_load = self.fig_actual_load.add_subplot(111)
        
        # 设置坐标轴样式 - 浅色主题配色
        self.ax_actual_load.set_facecolor('#fafafa')  # 浅灰色背景
        self.ax_actual_load.spines['bottom'].set_color('#b0bec5')  # 浅灰边框
        self.ax_actual_load.spines['top'].set_color('#b0bec5')
        self.ax_actual_load.spines['left'].set_color('#b0bec5')
        self.ax_actual_load.spines['right'].set_color('#b0bec5')
        self.ax_actual_load.tick_params(colors='#546e7a', which='both')  # 深灰色刻度
        self.ax_actual_load.xaxis.label.set_color('#2c3e50')  # 深色标签
        self.ax_actual_load.yaxis.label.set_color('#2c3e50')
        self.ax_actual_load.title.set_color('#2c3e50')  # 深色标题
        
        # 网格线样式
        self.ax_actual_load.grid(True, linestyle='--', alpha=0.3, color='#cfd8dc')
        
        # 创建画布框架容器
        canvas_container = ttk.Frame(self.actual_load_figure_frame)
        canvas_container.pack(fill=tk.BOTH, expand=True)
        
        # 创建画布
        self.canvas_actual_load = FigureCanvasTkAgg(self.fig_actual_load, master=canvas_container)
        canvas_widget = self.canvas_actual_load.get_tk_widget()
        canvas_widget.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        
        # 配置画布以自适应大小
        canvas_widget.configure(relief=tk.FLAT, bd=0)
        
        # 在图表右上角创建一个框架来放置工具栏 - 清新半透明背景
        toolbar_frame = tk.Frame(canvas_widget, bg='#ffffff', relief='flat', bd=1)
        toolbar_frame.place(relx=0.985, rely=0.02, anchor='ne')
        
        # 在图表左上角创建一个框架来放置按钮 - 清新半透明背景
        button_frame = tk.Frame(canvas_widget, bg='#ffffff', relief='flat')
        button_frame.place(relx=0.015, rely=0.02, anchor='nw')
        
        # 创建图表按钮样式 - 浅色清新风
        chart_button_style = {
            'font': ('Microsoft YaHei', 10, 'bold'),
            'bg': '#64b5f6',
            'fg': '#ffffff',
            'activebackground': '#42a5f5',
            'activeforeground': '#ffffff',
            'relief': 'raised',
            'borderwidth': 1,
            'padx': 12,
            'pady': 6,
            'cursor': 'hand2'
        }
        
        # 添加刷新按钮
        refresh_button = tk.Button(button_frame, text="🔄 刷新", command=self.refresh_plot, **chart_button_style)
        refresh_button.pack(side=tk.LEFT, padx=3, pady=3)
        
        # 添加滤波按钮
        filter_button = tk.Button(button_frame, text="🎛️ 滤波", command=self.apply_filter, **chart_button_style)
        filter_button.pack(side=tk.LEFT, padx=3, pady=3)
        
        # 添加微调按钮
        self.adjustment_button = tk.Button(button_frame, text="✏️ 微调", command=self.toggle_adjustment_mode, **chart_button_style)
        self.adjustment_button.pack(side=tk.LEFT, padx=3, pady=3)
        
        # 添加微调帮助按钮 - 小图标
        help_button_style = chart_button_style.copy()
        help_button_style['padx'] = 8
        adjustment_help_button = tk.Button(button_frame, text="❓", command=self.show_adjustment_help, **help_button_style)
        adjustment_help_button.pack(side=tk.LEFT, padx=2, pady=3)
        
        # 添加合并按钮
        self.merge_button = tk.Button(button_frame, text="🔗 合并", command=self.merge_selected_intervals, **chart_button_style)
        self.merge_button.pack(side=tk.LEFT, padx=3, pady=3)
        
        # 添加添加区间按钮
        self.add_interval_button = tk.Button(button_frame, text="➕ 添加", command=self.add_new_interval, **chart_button_style)
        self.add_interval_button.pack(side=tk.LEFT, padx=3, pady=3)
        
        # 添加导航工具栏到右上角
        self.toolbar_actual_load = NavigationToolbar2Tk(self.canvas_actual_load, toolbar_frame)
        self.toolbar_actual_load.update()
        # 调整工具栏样式使其更紧凑
        self.toolbar_actual_load.config(bg='#ffffff')
        for child in self.toolbar_actual_load.winfo_children():
            try:
                child.config(bg='#ffffff')
            except:
                pass
        
        # 初始化时就绑定鼠标交互事件
        self.setup_chart_interactions()
    
    def setup_chart_interactions(self):
        """设置图表交互功能（缩放、滚动、平移等）"""
        # 如果已经绑定了，先断开
        if self.scroll_cid:
            self.canvas_actual_load.mpl_disconnect(self.scroll_cid)
        if self.press_cid:
            self.canvas_actual_load.mpl_disconnect(self.press_cid)
        if self.release_cid:
            self.canvas_actual_load.mpl_disconnect(self.release_cid)
        if self.motion_cid:
            self.canvas_actual_load.mpl_disconnect(self.motion_cid)
        
        # 重新绑定事件
        self.scroll_cid = self.canvas_actual_load.mpl_connect('scroll_event', self.on_scroll_zoom)
        self.press_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_pan_press)
        self.release_cid = self.canvas_actual_load.mpl_connect('button_release_event', self.on_pan_release)
        self.motion_cid = self.canvas_actual_load.mpl_connect('motion_notify_event', self.on_pan_motion)
        
        # 保存当前视图范围
        if hasattr(self, 'ax_actual_load') and self.ax_actual_load.get_xlim() != (0.0, 1.0):
            self.original_xlim = self.ax_actual_load.get_xlim()
            self.original_ylim = self.ax_actual_load.get_ylim()
    
    def set_xticks_for_line_numbers(self):
        """统一设置横轴刻度标签"""
        unique_line_numbers = self.actual_load_unique_line_numbers
        if len(unique_line_numbers) == 1:
            n = unique_line_numbers[0]
            self.ax_actual_load.set_xticks([n, n+0.5, n+1])
            self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"])
        elif len(unique_line_numbers) > 20:
            step = max(1, len(unique_line_numbers) // 10)
            tick_positions = [unique_line_numbers[i] for i in range(0, len(unique_line_numbers), step)]
            self.ax_actual_load.set_xticks(tick_positions)
            self.ax_actual_load.set_xticklabels([str(ln) for ln in tick_positions], rotation=45)
        else:
            self.ax_actual_load.set_xticks(unique_line_numbers)
            self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], rotation=45)

    def butter_lowpass_filter(self, data, cutoff, fs, order=4):
        """应用巴特沃斯低通滤波器"""
        try:
            nyq = 0.5 * fs
            normal_cutoff = cutoff / nyq
            b, a = butter(order, normal_cutoff, btype='low', analog=False)
            y = filtfilt(b, a, data)
            return y
        except ImportError:
            messagebox.showwarning("警告", "未找到SciPy库，使用简单的移动平均滤波")
            window_size = int(1 / cutoff)
            if window_size < 3:
                window_size = 3
            return np.convolve(data, np.ones(window_size)/window_size, mode='same')
    
    def recommend_filter_params(self, data):
        """智能推荐滤波参数"""
        y = np.asarray(data)
        if len(y) < 10:
            return 0.1, 4
        
        # 估计数据的主要频率成分
        dy = np.diff(y)
        # 计算噪声水平
        noise_std = np.std(dy)
        # 计算信号变化率
        signal_std = np.std(y)
        
        # 根据信噪比推荐参数
        if signal_std > 1e-9:
            snr = abs(np.mean(y)) / noise_std if noise_std > 1e-9 else 100
        else:
            snr = 1.0
        
        # SNR高 -> 数据平稳 -> 可以用较低的截止频率
        # SNR低 -> 数据噪声大 -> 需要较强的滤波
        if snr > 50:
            cutoff = 0.15  # 轻度滤波
            order = 3
        elif snr > 20:
            cutoff = 0.1   # 中度滤波
            order = 4
        elif snr > 10:
            cutoff = 0.05  # 强滤波
            order = 5
        else:
            cutoff = 0.03  # 极强滤波
            order = 6
        
        return cutoff, order

    def apply_filter(self):
        """应用低通滤波器到数据（全自动推荐参数）"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        try:
            # 自动推荐参数
            cutoff, order = self.recommend_filter_params(self.actual_load_data)
            
            # 计算数据统计信息用于显示
            data_array = np.asarray(self.actual_load_data)
            dy = np.diff(data_array)
            noise_std = np.std(dy)
            signal_std = np.std(data_array)
            
            # 应用滤波
            fs = 1.0
            filtered_data = self.butter_lowpass_filter(data_array, cutoff, fs, order)
            
            # 保存滤波数据
            self.filtered_data = filtered_data
            self.is_filtered = True
            self.cutoff_freq.set(cutoff)
            self.filter_order.set(order)
            
            # 保存到程序数据
            if self.current_program_id and self.current_program_id in self.programs_data:
                prog_data = self.programs_data[self.current_program_id]
                prog_data['filtered_data'] = filtered_data
                prog_data['is_filtered'] = True
                prog_data['cutoff_freq'] = cutoff
                prog_data['filter_order'] = order
            
            # 绘制最终结果
            self.ax_actual_load.clear()
            self.ax_actual_load.plot(self.actual_load_x_positions, data_array, 
                                    color='#90caf9', linewidth=1.0, alpha=0.6, label='原始数据')
            self.ax_actual_load.plot(self.actual_load_x_positions, filtered_data, 
                                    color='#f44336', linewidth=2.0, label='滤波后数据', alpha=0.85)
            self.ax_actual_load.set_title('负载电流数据 (智能滤波)')
            self.ax_actual_load.set_xlabel('程序行号位置')
            self.ax_actual_load.set_ylabel('电流值')
            self.set_xticks_for_line_numbers()
            self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
            self.ax_actual_load.legend(loc='upper right')
            self.canvas_actual_load.draw()
            
            # 计算滤波效果评估
            original_noise = np.std(np.diff(data_array))
            filtered_noise = np.std(np.diff(filtered_data))
            noise_reduction = (1 - filtered_noise / original_noise) * 100 if original_noise > 1e-9 else 0
            
            # 显示详细信息
            info_msg = f"""✓ 智能滤波完成！

【滤波参数】（自动推荐）
• 截止频率: {cutoff:.3f}
• 滤波器阶数: {order}

【滤波效果】
• 噪声降低: {noise_reduction:.1f}%
• 原始噪声水平: {original_noise:.6f}
• 滤波后噪声: {filtered_noise:.6f}

【数据特征】
• 数据点数: {len(data_array)}
• 信号标准差: {signal_std:.4f}

💡 提示：
滤波后可以直接进行"自动划分"分析
如需恢复原始数据，点击"🔄 刷新"按钮"""
            
            messagebox.showinfo("智能滤波完成", info_msg)
            self.status_var_actual_load.set(f"✓ 智能滤波成功! 截止频率: {cutoff:.3f}, 阶数: {order}, 噪声降低: {noise_reduction:.1f}%")
            
        except Exception as e:
            messagebox.showerror("滤波错误", f"应用滤波时发生错误:\n{str(e)}")
            self.status_var_actual_load.set("❌ 滤波失败")
            import traceback
            traceback.print_exc()

    def get_current_data(self):
        """获取当前使用的数据（原始或滤波后）"""
        if self.is_filtered and self.filtered_data is not None:
            return self.filtered_data
        else:
            return self.actual_load_data
    
    def estimate_noise_level(self, data):
        """估计数据的噪声水平，使用相邻点差值的标准差"""
        if len(data) < 3:
            return 0
        diffs = np.abs(np.diff(data))
        return np.std(diffs)
    
    # ========== 自动参数标定与自动分析方法 ==========
    
    def auto_calibrate_params(self, data):
        """自动参数标定 - 从数据自身估计合适的阈值和最小区间长度（改进版）
        
        参数:
            data: 数据序列（列表或numpy数组）
        
        返回:
            dict: 包含 abs_thr, rel_thr, min_len, slope_thr 的字典
        """
        y = np.asarray(data)
        if len(y) < 10:
            # 数据太少，返回默认值
            return dict(abs_thr=0.05, rel_thr=0.05, min_len=min(100, len(y)//2), slope_thr=0.01)
        
        # 改进的噪声估计：使用分位数方法更鲁棒
        dy = np.diff(y)
        if len(dy) > 4:
            # 使用第10和第90百分位数之间的差值估计噪声范围
            p10, p90 = np.percentile(np.abs(dy), [10, 90])
            # 使用MAD方法
            mad_dy = np.median(np.abs(dy - np.median(dy)))
            # 综合两种方法
            sigma_d = max(1.4826 * mad_dy, (p90 - p10) / 2.56) if mad_dy > 1e-9 else np.std(dy)
        else:
            sigma_d = np.std(dy)
        
        if sigma_d < 1e-9:
            sigma_d = 1e-9
        
        # 使用数据的中位数而非绝对值的中位数，更准确反映信号强度
        med_y = np.median(y)
        if abs(med_y) < 1e-9:
            med_y = np.mean(np.abs(y))
            if med_y < 1e-9:
                med_y = 1e-9
        
        # 获取灵敏度参数（用户可通过UI调整）
        # 为了让滑块标度为1时不显得过于灵敏，使用对原始灵敏度的平滑映射：
        # effective_s = 1 + 0.5*(s_raw - 1)
        # 这样滑块偏离1时对阈值的影响减弱一半，用户仍可通过扩大滑块范围进行调节
        s_raw = self.auto_sensitivity.get()
        try:
            s_raw = float(s_raw)
        except Exception:
            s_raw = 1.0
        # 新映射：使得滑块为1时的实际灵敏度为0.5
        # effective_s = 0.5 * s_raw
        effective_s = 0.5 * s_raw
        # 防止过小或为0
        s = max(0.1, effective_s)
        
        # 自适应阈值系数：根据数据的变异系数(CV)调整
        cv = sigma_d / (abs(med_y) + 1e-9)
        # CV越大，说明数据波动越大，需要放宽阈值
        k_abs_adaptive = 3.0 + min(2.0, cv * 10)  # 3.0-5.0之间自适应
        k_rel_adaptive = 4.0 + min(3.0, cv * 15)  # 4.0-7.0之间自适应
        
        # 计算绝对阈值
        abs_thr = (k_abs_adaptive / s) * sigma_d
        
        # 计算相对阈值
        rel_thr = np.clip((k_rel_adaptive / s) * (sigma_d / abs(med_y)), 0.015, 0.35)
        
        # 改进的最小区间长度估计
        run_mask = np.abs(dy) <= sigma_d * 1.5  # 使用稍宽松的阈值统计run-length
        runs = []
        cnt = 1
        for i in range(len(run_mask)):
            if run_mask[i]:
                cnt += 1
            else:
                if cnt > 1:  # 只记录有效的run
                    runs.append(cnt)
                cnt = 1
        if cnt > 1:
            runs.append(cnt)
        
        program_length = len(y)
        
        # 更智能的最小区间长度计算
        if len(runs) > 10:
            # 使用run-length的统计信息
            stat_min_len = int(np.percentile(runs, 60))  # 降低到P60
            # 根据程序长度和run统计动态调整
            adaptive_factor = np.clip(0.8 + (program_length / 100000), 0.8, 2.0)
            min_len_base = int(stat_min_len * adaptive_factor)
        else:
            # 如果run统计不够，使用基于程序长度的估计
            # 短程序用更小的比例，长程序用更大的比例
            if program_length < 10000:
                percentage = 0.01  # 1%
            elif program_length < 50000:
                percentage = 0.012  # 1.2%
            else:
                percentage = 0.015  # 1.5%
            min_len_base = int(program_length * percentage)
        
        # 动态边界：根据程序长度设置
        if program_length < 5000:
            min_bound = 50
            max_bound = 500
        elif program_length < 20000:
            min_bound = 100
            max_bound = 800
        elif program_length < 100000:
            min_bound = 200
            max_bound = 1200
        else:
            min_bound = 300
            max_bound = 2000
        
        min_len = int(np.clip(min_len_base, min_bound, max_bound))
        
        # 斜率阈值：也需要根据数据特征自适应
        slope_thr = (1.5 * k_abs_adaptive / s) * sigma_d
        
        return dict(abs_thr=abs_thr, rel_thr=rel_thr, min_len=min_len, slope_thr=slope_thr)
    
    def propose_intervals_auto(self, data, abs_thr, rel_thr, min_len, slope_thr):
        """候选生成 - 无依赖版本，基于滑窗平稳性判定 + 贪心扩张
        
        参数:
            data: 数据序列
            abs_thr: 绝对阈值
            rel_thr: 相对阈值
            min_len: 最小区间长度
            slope_thr: 斜率阈值
        
        返回:
            List[Tuple[int, int]]: 稳态区间列表
        """
        y = np.asarray(data)
        n = len(y)
        if n == 0:
            return []
        
        intervals = []
        left = 0
        
        while left < n:
            min_deque = collections.deque()
            max_deque = collections.deque()
            right = left
            sum_y = 0.0
            # 线性回归增量统计
            sum_x = sum_x2 = sum_xy = 0.0
            
            while right < n:
                val = y[right]
                sum_y += val
                
                # 更新队列
                while min_deque and min_deque[-1] > val:
                    min_deque.pop()
                while max_deque and max_deque[-1] < val:
                    max_deque.pop()
                min_deque.append(val)
                max_deque.append(val)
                
                # 增量回归（x用索引）
                x = right - left + 1
                sum_x += x
                sum_x2 += x * x
                sum_xy += x * val
                
                length = right - left + 1
                mean = sum_y / length
                rng = max_deque[0] - min_deque[0]
                
                # slope ~ (n*sum_xy - sum_x*sum_y)/(n*sum_x2 - sum_x^2)
                denom = (length * sum_x2 - sum_x * sum_x)
                if abs(denom) > 1e-9:
                    slope = abs((length * sum_xy - sum_x * sum_y) / denom)
                else:
                    slope = 0.0
                
                cond_abs = rng <= abs_thr
                cond_rel = rng <= rel_thr * max(1e-9, abs(mean))
                cond_slp = slope <= slope_thr
                
                if (cond_abs or cond_rel) and cond_slp:
                    right += 1
                else:
                    break
            
            if right - left >= min_len:
                intervals.append((left, right - 1))
            
            left = max(right, left + 1)
        
        # 记录原始检测到的小区间（在任何后处理前）
        raw_intervals = intervals.copy()

        # 合并近邻 & 去重重叠（复用已有方法）
        if intervals:
            # 动态计算合并间隙：根据最小区间长度和数据特征
            # 对于稳态区间，小间隙应该被合并
            max_gap = max(1, int(0.15 * min_len))  # 从20%降至15%，更积极地合并
            intervals = self.merge_close_intervals(intervals, max_gap, min_len)
            intervals = self.adjust_overlapping_intervals(intervals, overlap_tolerance=10)

            # 自动裁边（使用适中的阈值，避免过度裁剪）
            trimmed = []
            for s, e in intervals:
                rs, re = self.reduce_interval_boundaries(
                    data=y, start=s, end=e,
                    threshold=rel_thr * 0.7,  # 从0.6提高到0.7，减少过度裁剪
                    abs_threshold=abs_thr * 0.7  # 从0.6提高到0.7
                )
                if re - rs + 1 >= min_len:
                    trimmed.append((rs, re))
            intervals = trimmed

        # 如果识别到很多短小区间，尝试按更大粒度分组并扩展区间边界
        # 目的：当算法捕获到许多只覆盖波峰的小区间时，合并为更符合人工标注的大区块
        try:
            if intervals:
                avg_len = np.mean([e - s + 1 for s, e in intervals])
                # 条件：平均区间长度小于2倍最小长度且区间数量较多
                if avg_len < 2 * min_len and len(intervals) >= 3:
                    # 计算自适应分组间隙（受程序长度影响）
                    group_gap = max(int(0.2 * min_len), int(0.005 * n), 50)
                    # 进一步限制最大组间隙，避免全局合并
                    group_gap = min(group_gap, int(0.5 * n))
                    intervals = self.group_intervals_into_blocks(intervals, group_gap)

                    # 对每个分组扩展边界，尝试包含低谷区域使平均功率更接近真实
                    expanded = []
                    for s, e in intervals:
                        rs, re = self.expand_block_edges(y, s, e, max_expand=int(0.5 * min_len),
                                                         rel_thr=rel_thr, abs_thr=abs_thr)
                        # 保证扩展后仍满足最小长度要求
                        if re - rs + 1 >= min_len:
                            expanded.append((rs, re))
                        else:
                            expanded.append((s, e))
                    intervals = expanded
        except Exception:
            # 若任何步骤异常，保留之前的 intervals
            pass

        # 计算有效灵敏度（与 auto_calibrate_params 保持一致的映射）
        try:
            s_raw = float(getattr(self, 'auto_sensitivity').get())
        except Exception:
            s_raw = 1.0
        # 映射与 auto_calibrate_params 保持一致：滑块1对应effective_s=0.5
        effective_s = 0.5 * s_raw

        # 如果用户希望保留所有检测到的小区间（更敏感模式），直接返回 raw_intervals
        mode = getattr(self, 'interval_mode', 'large_coverage')
        if mode == 'all_small':
            # 只保留满足最小长度的原始区间，并按起点排序
            filtered = [iv for iv in raw_intervals if iv[1] - iv[0] + 1 >= min_len]
            filtered.sort(key=lambda x: x[0])
            return filtered

        # large_coverage 模式：在已有处理的基础上，如果覆盖率仍然低，尝试按覆盖率合并
        if mode == 'large_coverage':
            total_cov = 0
            if intervals:
                total_cov = sum(e - s + 1 for s, e in intervals) / float(n)
            # 如果覆盖率低于目标，逐步合并最近的区间直到达到目标或没有更多可合并的间隙
            target = getattr(self, 'target_coverage', 0.65)
            # 当灵敏度较高（effective_s >= 1），降低合并目标以避免过度合并
            if effective_s >= 1.0:
                # 高灵敏度时，只尝试达到较低的覆盖率上限
                merge_target = max(0.2, target * 0.6)
            else:
                # 低灵敏度时，允许接近目标覆盖率
                merge_target = target

            if total_cov < merge_target and intervals:
                # 传入灵敏度因子（倒数）以控制合并/扩展的激进程度
                sensitivity_factor = max(0.2, 1.0 / effective_s)
                intervals = self.merge_intervals_until_coverage(intervals, n, merge_target, getattr(self, 'max_merge_gap_ratio', 0.02), sensitivity_factor)

        return intervals
    
    def analyze_auto(self):
        """一键全自动划分入口 - 零参数可用"""
        if not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        try:
            # 确定使用原始数据还是滤波数据
            if self.is_filtered and self.filtered_data is not None:
                analysis_data = self.filtered_data
                data_type = "滤波"
            else:
                analysis_data = self.actual_load_data
                data_type = "原始"
            
            # 自动标定参数
            params = self.auto_calibrate_params(analysis_data)
            
            # 保存当前灵敏度到刀具数据
            if self.current_program_id and self.current_tool_key:
                if self.current_program_id in self.programs_data:
                    if self.current_tool_key in self.programs_data[self.current_program_id]:
                        self.programs_data[self.current_program_id][self.current_tool_key]['auto_sensitivity'] = self.auto_sensitivity.get()
            
            # 生成候选区间
            ivs = self.propose_intervals_auto(
                analysis_data,
                params['abs_thr'],
                params['rel_thr'],
                params['min_len'],
                params['slope_thr']
            )
            
            # 如果没有找到区间，尝试降低灵敏度再试一次
            if not ivs:
                original_sensitivity = self.auto_sensitivity.get()
                self.auto_sensitivity.set(original_sensitivity * 0.8)
                params = self.auto_calibrate_params(analysis_data)
                ivs = self.propose_intervals_auto(
                    analysis_data,
                    params['abs_thr'],
                    params['rel_thr'],
                    params['min_len'],
                    params['slope_thr']
                )
                # 恢复灵敏度设置
                self.auto_sensitivity.set(original_sensitivity)
            
            if not ivs:
                messagebox.showinfo("自动分析", "未能找到稳态区间，请尝试调整灵敏度或使用手动分析")
                return
            
            # 更新区间结果
            self.actual_load_intervals = ivs
            
            # 合并所有重叠区间
            processed = self.merge_all_overlapping_intervals()
            if processed > 0:
                self.status_var_actual_load.set(f"自动分析完成，合并了 {processed} 个重叠区间")
            
            self.current_intervals = list(self.actual_load_intervals)
            
            # 保存区间到程序数据（关键：必须在refresh_interval_ui之前保存）
            if self.current_program_id and self.current_tool_key:
                if self.current_program_id in self.programs_data:
                    if self.current_tool_key in self.programs_data[self.current_program_id]:
                        self.programs_data[self.current_program_id][self.current_tool_key]['intervals'] = self.actual_load_intervals.copy()

            # 绘制结果
            self.plot_steady_intervals("自动")

            # 刷新区间详情与平均值并保存状态
            self.refresh_interval_ui("自动")

            # 如果处于微调模式，更新边界线
            if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
                self.draw_interval_boundaries()
            
            # 刷新刀具选择器显示，显示✓标记（保持当前选择）
            if hasattr(self, 'current_program_id') and self.current_program_id:
                self.update_tool_selector(self.current_program_id, preserve_selection=True)
            
            # 注意：不在这里调用update_all_intervals_summary()，因为会覆盖刚显示的详细区间信息
            # 汇总信息只在用户主动切换到其他视图时显示
            
            # 显示自动标定的参数信息
            # 计算数据的统计信息
            data_mean = np.mean(analysis_data)
            data_std = np.std(analysis_data)
            data_cv = (data_std / abs(data_mean) * 100) if abs(data_mean) > 1e-9 else 0
            
            info_msg = f"""✓ 自动分析完成！
            
【数据信息】
• 使用数据: {data_type}数据
• 数据点数: {len(analysis_data)}
• 平均值: {data_mean:.4f}
• 标准差: {data_std:.4f}
• 变异系数: {data_cv:.2f}%

【分析结果】
• 找到稳态区间: {len(ivs)} 个
• 总覆盖点数: {sum(e-s+1 for s,e in ivs)}
• 覆盖率: {sum(e-s+1 for s,e in ivs)/len(analysis_data)*100:.1f}%

【自动标定参数】
• 灵敏度: {self.auto_sensitivity.get():.1f}
• 绝对阈值: {params['abs_thr']:.4f}
• 相对阈值: {params['rel_thr']:.3f} ({params['rel_thr']*100:.1f}%)
• 斜率阈值: {params['slope_thr']:.6f}

💡 如需微调:
  - 调整灵敏度滑块后重新分析
  - 或使用"微调"功能手动调整边界"""
            messagebox.showinfo("自动分析完成", info_msg)
            
        except Exception as e:
            messagebox.showerror("自动分析错误", f"自动分析过程中发生错误:\n{str(e)}")
            import traceback
            traceback.print_exc()
        
    def merge_close_intervals(self, intervals, max_gap, min_length=1):
        """合并间隔小于或等于max_gap的相邻区间，并过滤掉小于min_length的区间"""
        if not intervals or len(intervals) < 2:
            # 过滤单个区间的长度
            return [iv for iv in intervals if (iv[1] - iv[0] + 1) >= min_length]
            
        # 按起始位置排序
        intervals.sort(key=lambda x: x[0])
        
        merged = []
        current_start, current_end = intervals[0]
        
        for next_start, next_end in intervals[1:]:
            if next_start - current_end <= max_gap + 1:
                # 合并区间
                current_end = max(current_end, next_end)
            else:
                # 保存当前区间（仅保存满足最小长度的区间）
                if current_end - current_start + 1 >= min_length:
                    merged.append((current_start, current_end))
                current_start, current_end = next_start, next_end
                
        # 添加最后一个区间（仅当满足最小长度时）
        if current_end - current_start + 1 >= min_length:
            merged.append((current_start, current_end))
        
        return merged
    
    def adjust_overlapping_intervals(self, intervals, overlap_tolerance=10):
        """调整重叠的区间边界，消除重叠"""
        if not intervals or len(intervals) < 2:
            return intervals
        intervals.sort(key=lambda x: x[0])
        adjusted = []
        for interval in intervals:
            curr_start, curr_end = interval
            if not adjusted:
                adjusted.append((curr_start, curr_end))
                continue
            prev_start, prev_end = adjusted[-1]
            if curr_start <= prev_end:
                overlap_midpoint = (prev_end + curr_start) // 2
                new_prev_end = overlap_midpoint
                new_curr_start = overlap_midpoint + 1
                prev_valid = (new_prev_end >= prev_start)
                curr_valid = (new_curr_start <= curr_end)
                if prev_valid and curr_valid:
                    adjusted[-1] = (prev_start, new_prev_end)
                    adjusted.append((new_curr_start, curr_end))
                elif prev_valid and not curr_valid:
                    adjusted[-1] = (prev_start, new_prev_end)
                elif not prev_valid and curr_valid:
                    adjusted[-1] = (new_curr_start, curr_end)
                else:
                    prev_length = prev_end - prev_start + 1
                    curr_length = curr_end - curr_start + 1
                    if curr_length > prev_length:
                        adjusted[-1] = (curr_start, curr_end)
            else:
                adjusted.append((curr_start, curr_end))
        validated = []
        for start, end in adjusted:
            if start <= end:
                validated.append((start, end))
        return validated

    def group_intervals_into_blocks(self, intervals, max_gap):
        """将多个短小且彼此接近的区间分组为更大的区块。

        intervals: 已排序或未排序的区间列表 [(s,e),...]
        max_gap: 当两个区间之间的间隙 <= max_gap 时，将它们视为同一组
        返回合并后的区块列表
        """
        if not intervals:
            return []
        intervals = sorted(intervals, key=lambda x: x[0])
        grouped = []
        cur_s, cur_e = intervals[0]
        for s, e in intervals[1:]:
            gap = s - cur_e - 1
            if gap <= max_gap:
                # 合并到当前区块
                cur_e = max(cur_e, e)
            else:
                grouped.append((cur_s, cur_e))
                cur_s, cur_e = s, e
        grouped.append((cur_s, cur_e))
        return grouped

    def expand_block_edges(self, data, start, end, max_expand=100, rel_thr=0.05, abs_thr=0.05):
        """在不显著增加波动范围的前提下向外扩展区块边界。

        data: numpy array
        start,end: 原区块索引
        max_expand: 单侧最大扩展点数
        rel_thr, abs_thr: 扩展时允许的相对/绝对波动阈值（与propose_intervals_auto传入的一致）
        返回扩展后的 (new_start, new_end)
        """
        n = len(data)
        new_s, new_e = start, end
        baseline = np.mean(data[start:end+1])

        # 向左扩展
        left_expand = 0
        for i in range(1, max_expand+1):
            idx = start - i
            if idx < 0:
                break
            seg = data[idx:new_e+1]
            seg_mean = np.mean(seg)
            seg_rng = np.max(seg) - np.min(seg)
            cond_rel = (seg_rng <= rel_thr * max(1e-9, abs(seg_mean)))
            cond_abs = (seg_rng <= abs_thr)
            if cond_rel or cond_abs:
                new_s = idx
                left_expand += 1
            else:
                break

        # 向右扩展
        right_expand = 0
        for i in range(1, max_expand+1):
            idx = end + i
            if idx >= n:
                break
            seg = data[new_s:idx+1]
            seg_mean = np.mean(seg)
            seg_rng = np.max(seg) - np.min(seg)
            cond_rel = (seg_rng <= rel_thr * max(1e-9, abs(seg_mean)))
            cond_abs = (seg_rng <= abs_thr)
            if cond_rel or cond_abs:
                new_e = idx
                right_expand += 1
            else:
                break

        return max(0, new_s), min(n-1, new_e)

    def merge_intervals_until_coverage(self, intervals, data_len, target_coverage, max_merge_gap_ratio=0.02, sensitivity_factor=1.0):
        """按覆盖率合并区间：优先合并间隙最小的相邻区间，直到达到目标覆盖率或无法继续合并。

        intervals: List[(s,e)] 已排序或未排序
        data_len: 数据总长度
        target_coverage: 目标覆盖率，0-1
        max_merge_gap_ratio: 允许合并的最大间隙比例（相对于数据长度），用于避免跨越巨大空白
        返回合并后的区间列表
        """
        if not intervals:
            return []

        intervals = sorted(intervals, key=lambda x: x[0])

        def coverage(iv_list):
            return sum(e - s + 1 for s, e in iv_list) / float(max(1, data_len))

        cur_cov = coverage(intervals)
        # 根据灵敏度调整允许的合并间隙（灵敏度因子>1时更容易合并）
        allowed_gap = max(1, int(max_merge_gap_ratio * data_len * sensitivity_factor))

        # 防止过度跨域合并，设置一个硬限制（最大允许合并间隙倍数）
        max_allowed_gap = max(allowed_gap, int(0.01 * data_len))
        # 根据灵敏度缩放上限
        max_allowed_gap = int(max(max_allowed_gap, allowed_gap * 10 * sensitivity_factor))

        # 逐步合并最小间隙的相邻区间（第一阶段：保守合并）
        while cur_cov < target_coverage and len(intervals) > 1:
            # 计算相邻间隙
            gaps = []  # (gap, idx)
            for i in range(len(intervals) - 1):
                s1, e1 = intervals[i]
                s2, e2 = intervals[i + 1]
                gap = s2 - e1 - 1
                gaps.append((gap, i))

            # 找到最小间隙对
            gaps.sort(key=lambda x: x[0])
            if not gaps:
                break

            smallest_gap, idx = gaps[0]

            # 如果最小间隙太大（超过阈值的若干倍），停止合并以避免合并不相干区域
            if smallest_gap > max_allowed_gap:
                break

            # 合并 idx 和 idx+1
            s1, e1 = intervals[idx]
            s2, e2 = intervals[idx + 1]
            new_iv = (s1, e2)

            # 重建列表
            new_list = intervals[:idx] + [new_iv] + intervals[idx + 2:]
            intervals = new_list

            # 更新覆盖率
            cur_cov = coverage(intervals)

        # 如果第一阶段仍未达到目标，进入第二阶段：更激进的合并与扩展
        if cur_cov < target_coverage:
            # 允许更大的间隙进行合并（使用对象属性的aggressive比例作为建议）
            try:
                aggressive_ratio = getattr(self, 'aggressive_merge_gap_ratio', max_merge_gap_ratio * 2)
            except Exception:
                aggressive_ratio = max_merge_gap_ratio * 2
            # 激进阶段也遵循灵敏度因子
            max_allowed_gap = max(1, int(aggressive_ratio * data_len * sensitivity_factor))

            # 继续合并最小间隙对，但不超过新的阈值
            merged_flag = False
            while cur_cov < target_coverage and len(intervals) > 1:
                # 重新计算相邻间隙并选择最小的
                gaps = []
                for i in range(len(intervals) - 1):
                    s1, e1 = intervals[i]
                    s2, e2 = intervals[i + 1]
                    gap = s2 - e1 - 1
                    gaps.append((gap, i))

                if not gaps:
                    break
                gaps.sort(key=lambda x: x[0])
                smallest_gap, idx = gaps[0]
                if smallest_gap > max_allowed_gap:
                    break

                # 合并邻区
                s1, e1 = intervals[idx]
                s2, e2 = intervals[idx + 1]
                new_iv = (s1, e2)
                intervals = intervals[:idx] + [new_iv] + intervals[idx + 2:]
                cur_cov = coverage(intervals)
                merged_flag = True

            # 如果仍未满足覆盖率，尝试扩展每个区间的边界以包含更多点
            if cur_cov < target_coverage:
                try:
                    expand_ratio = getattr(self, 'expand_ratio_for_coverage', 0.5)
                except Exception:
                    expand_ratio = 0.5

                # 估计每侧最大扩展点数（基于平均区间长度或min_len），并按灵敏度放缩
                avg_len = int(np.mean([e - s + 1 for s, e in intervals])) if intervals else 0
                # 在低灵敏度时允许更大扩展；sensitivity_factor>1 表示更容易合并/扩展
                max_expand = max(1, int(expand_ratio * max(avg_len, int(0.01 * data_len)) * sensitivity_factor))

                expanded = []
                for s, e in intervals:
                    # 直接按最大扩展步数向外扩展（每侧扩展 max_expand 点），然后裁边到数据范围
                    new_s = max(0, s - max_expand)
                    new_e = min(data_len - 1, e + max_expand)
                    expanded.append((new_s, new_e))

                # 合并可能重叠的扩展区间
                intervals = self.merge_close_intervals(expanded, max_gap=0, min_length=1)
                cur_cov = coverage(intervals)

        return intervals
        

    def update_all_intervals_summary(self):
        """更新稳态区间详情，显示所有已划分的程序和刀具汇总信息"""
        self.actual_load_result_text.delete(1.0, tk.END)
        
        # 统计所有已划分的程序和刀具
        total_tools = 0
        total_intervals = 0
        program_stats = {}  # {program_name: {'tools': set(), 'intervals': count}}
        
        # 遍历所有programs_data统计已划分的刀具
        for program_id, prog_data_or_tools in self.programs_data.items():
            if not isinstance(prog_data_or_tools, dict):
                continue
            
            # 检查是否有刀具数据
            has_tools = False
            for key, value in prog_data_or_tools.items():
                if isinstance(value, dict) and 'tool_key' in value:
                    has_tools = True
                    break
            
            if has_tools:
                # 新格式：遍历所有刀具
                program_name = None
                for tool_key, tool_data in prog_data_or_tools.items():
                    if isinstance(tool_data, dict) and 'intervals' in tool_data and tool_data['intervals']:
                        if program_name is None:
                            program_name = tool_data.get('name', 'Unknown')
                        
                        if program_name not in program_stats:
                            program_stats[program_name] = {'tools': set(), 'intervals': 0}
                        
                        tool_id = tool_data.get('tool_id', 'Unknown')
                        program_stats[program_name]['tools'].add(tool_id)
                        program_stats[program_name]['intervals'] += len(tool_data['intervals'])
                        total_tools += 1
                        total_intervals += len(tool_data['intervals'])
        
        # 显示汇总信息
        if total_tools == 0:
            self.actual_load_result_text.insert(tk.END, "📋 稳态区间汇总\n")
            self.actual_load_result_text.insert(tk.END, "=" * 60 + "\n\n")
            self.actual_load_result_text.insert(tk.END, "暂无已划分的稳态区间\n")
            self.actual_load_result_text.insert(tk.END, "请先选择程序和刀具进行自动划分或批量划分\n")
            return
        
        self.actual_load_result_text.insert(tk.END, "📋 稳态区间汇总 - 所有已划分的程序和刀具\n")
        self.actual_load_result_text.insert(tk.END, "=" * 60 + "\n\n")
        self.actual_load_result_text.insert(tk.END, f"✓ 总计: {len(program_stats)} 个程序, {total_tools} 个刀具, {total_intervals} 个区间\n\n")
        
        # 按照txt文件顺序显示每个程序的详细信息
        for program_id, program_info in self.program_mapping.items():
            program_name = program_info['name']
            
            if program_name in program_stats:
                stats = program_stats[program_name]
                tools_list_str = ', '.join(sorted(stats['tools']))
                
                self.actual_load_result_text.insert(tk.END, f"▸ {program_name}\n")
                self.actual_load_result_text.insert(tk.END, f"  刀具: {tools_list_str}\n")
                self.actual_load_result_text.insert(tk.END, f"  已划分: {len(stats['tools'])} 个刀具, {stats['intervals']} 个区间\n\n")
        
        self.actual_load_result_text.insert(tk.END, "-" * 60 + "\n")
        self.actual_load_result_text.insert(tk.END, "💡 点击左侧程序选择器可查看具体刀具的区间详情\n")

    def refresh_interval_ui(self, data_type):
        """统一刷新稳态区间详情与页面平均值，并保存状态"""
        try:
            reduce_flag = self.reduce_interval_actual_load.get() if hasattr(self, 'reduce_interval_actual_load') else False
        except Exception:
            reduce_flag = False

        # 刷新区间详情
        self.update_interval_display(data_type, reduce_flag)
        # update_interval_display内部已经调用了强制刷新

        # 刷新页面基准值（使用区间平均值）
        prog_data = None
        if getattr(self, 'current_program_id', None) and self.current_program_id in getattr(self, 'programs_data', {}):
            if hasattr(self, 'current_tool_key') and self.current_tool_key:
                prog_data = self.programs_data[self.current_program_id].get(self.current_tool_key)
            else:
                prog_data = self.programs_data[self.current_program_id]

        if prog_data:
            try:
                interval_avg = self.calculate_interval_average(prog_data)
                # 将区间平均值显示在界面上
                if hasattr(self, 'average_value_label') and self.average_value_label:
                    self.average_value_label.config(text=f"{interval_avg:.3f}")
                    try:
                        self.average_value_label.update_idletasks()
                    except Exception:
                        pass

                # 把计算得到的区间平均写回到数据结构中的基准值字段
                try:
                    # 支持刀具级别和程序级别两种数据结构
                    if hasattr(self, 'current_tool_key') and self.current_tool_key and self.current_program_id in self.programs_data and self.current_tool_key in self.programs_data[self.current_program_id]:
                        self.programs_data[self.current_program_id][self.current_tool_key]['average'] = float(interval_avg)
                    elif self.current_program_id in self.programs_data:
                        # 旧格式或程序级别
                        pd_ref = self.programs_data[self.current_program_id]
                        if isinstance(pd_ref, dict):
                            pd_ref['average'] = float(interval_avg)
                except Exception:
                    pass

                # 更新理想值显示（基准值变更后需同步更新）
                try:
                    self.update_ideal_value()
                except Exception:
                    pass
            except Exception:
                pass

        # 保存状态
        try:
            self.save_current_program_state()
        except Exception:
            pass

    def update_interval_display(self, data_type, reduce_interval):
        """更新区间显示"""
        self.actual_load_result_text.delete(1.0, tk.END)
        interval_count = len(self.actual_load_intervals) if self.actual_load_intervals else 0
        self.actual_load_result_text.insert(tk.END, f"使用{data_type}数据找到 {interval_count} 个稳态区间:\n\n")
        self.actual_load_result_text.insert(tk.END, "区间\t\t\t长度(点)\t平均值\n")
        self.actual_load_result_text.insert(tk.END, "-" * 80 + "\n")
        
        # 基础数据有效性检查
        if (self.actual_load_line_numbers is None or
            self.actual_load_point_indices is None or
            not isinstance(self.actual_load_line_numbers, (list, np.ndarray)) or
            not isinstance(self.actual_load_point_indices, (list, np.ndarray))):
            messagebox.showerror("数据缺失", "程序行号或点索引数据未正确加载，请先重新加载数据。")
            return
        
        if not self.actual_load_intervals:
            self.actual_load_result_text.insert(tk.END, "无可显示的区间。\n")
            return
        
        # 计算每个区间的平均值
        self.actual_load_interval_values = []
        if self.is_filtered and self.filtered_data is not None:
            analysis_data = self.filtered_data
        else:
            analysis_data = self.actual_load_data
        
        # 再次检查分析数据有效性
        if analysis_data is None or len(analysis_data) == 0:
            messagebox.showerror("数据缺失", "分析数据为空，请先加载并分析数据。")
            return
        
        data_len = len(analysis_data)
        line_len = len(self.actual_load_line_numbers)
        point_len = len(self.actual_load_point_indices)
        
        valid_interval_count = 0  # 记录有效区间数量
        
        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            # 索引边界保护
            if (start_idx < 0 or end_idx < 0 or
                start_idx >= data_len or end_idx >= data_len or
                start_idx >= line_len or end_idx >= line_len or
                start_idx >= point_len or end_idx >= point_len or
                start_idx > end_idx):
                continue  # 跳过异常区间
            
            try:
                # 计算区间平均值
                interval_data = analysis_data[start_idx:end_idx+1]
                interval_avg = np.mean(interval_data)
                self.actual_load_interval_values.append(interval_avg)
                
                # 获取程序行号和行内索引
                start_ln = self.actual_load_line_numbers[start_idx]
                start_point_idx = self.actual_load_point_indices[start_idx]
                end_ln = self.actual_load_line_numbers[end_idx]
                end_point_idx = self.actual_load_point_indices[end_idx]
                
                length_points = end_idx - start_idx + 1
                
                # 使用新格式显示区间，包含平均值
                self.actual_load_result_text.insert(
                    tk.END,
                    f"[{start_ln:.0f}.{start_point_idx}, {end_ln:.0f}.{end_point_idx}]\t"
                    f"{length_points}\t{interval_avg:.3f}\n"
                )
                valid_interval_count += 1
            except Exception:
                # 单个区间异常不影响其它区间
                continue
        
        # 只有当没有任何有效区间时才显示警告
        if valid_interval_count == 0:
            self.actual_load_result_text.insert(tk.END, "\n未能生成有效区间，请检查阈值设置或重新加载数据。\n")
        
        # 强制刷新文本区域，确保立即显示
        try:
            self.actual_load_result_text.update_idletasks()
            self.actual_load_result_text.update()
        except Exception:
            pass

    def plot_steady_intervals(self, data_type):
        """绘制稳态区间"""
        # 保存当前视图范围
        current_xlim = self.ax_actual_load.get_xlim()
        current_ylim = self.ax_actual_load.get_ylim()
        has_valid_view = (current_xlim != (0.0, 1.0))
        
        self.ax_actual_load.clear()
        # 空值防护
        if (self.actual_load_data is None or self.actual_load_x_positions is None or
                len(self.actual_load_data) == 0):
            self.ax_actual_load.text(0.5, 0.5, "无数据可绘制", ha='center', va='center')
            self.canvas_actual_load.draw()
            return
        
        # 绘制所有数据点 - 使用鲜艳的蓝色
        self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data,
                                 color='#2196F3', linewidth=1.8, label='负载电流值', alpha=0.9)
        
        # 如果有滤波数据，也绘制滤波后的数据
        if self.is_filtered and self.filtered_data is not None:
            self.ax_actual_load.plot(self.actual_load_x_positions, self.filtered_data,
                                     color='#f44336', linewidth=2.0, label='滤波后数据', alpha=0.85)
        
        # 标记稳态区间
        if self.actual_load_intervals:
            for start_idx, end_idx in self.actual_load_intervals:
                if start_idx < 0 or end_idx >= len(self.actual_load_x_positions):
                    continue
                start_x = self.actual_load_x_positions[start_idx]
                end_x = self.actual_load_x_positions[end_idx]
                self.ax_actual_load.axvspan(start_x, end_x, alpha=0.25, color='#a5d6a7', 
                                           edgecolor='#66bb6a', linewidth=1.5)
                
                # 添加纵向边界线
                self.ax_actual_load.axvline(x=start_x, color='#43a047', linewidth=0.8, alpha=0.7)
                self.ax_actual_load.axvline(x=end_x, color='#43a047', linewidth=0.8, alpha=0.7)
        
        # 已移除绝对阈值线的显示（基于输入参数）
        
        # 设置标题和标签
        title = f'负载电流稳态区间 ({data_type}数据)'
        ylabel = '电流 (A)'
        
        self.ax_actual_load.set_title(title)
        self.ax_actual_load.set_xlabel('程序行号位置')
        self.ax_actual_load.set_ylabel(ylabel)
        self.set_xticks_for_line_numbers()
        
        self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
        self.ax_actual_load.legend(loc='upper right')
        
        # 优化布局以充分利用图表区域
        self.fig_actual_load.subplots_adjust(
            left=0.06, bottom=0.08, right=0.98, top=0.96,
            wspace=0.1, hspace=0.1
        )
        
        # 恢复之前的视图范围（如果有的话）
        if has_valid_view:
            self.ax_actual_load.set_xlim(current_xlim)
            self.ax_actual_load.set_ylim(current_ylim)
        
        self.canvas_actual_load.draw()

    def identify_steady_state_intervals(self, data, min_length, threshold, abs_threshold, reduce_interval):
        """识别稳态区间 - 使用与copy3完全相同的算法"""
        intervals = []
        n = len(data)
        
        if n < min_length:
            return intervals
        
        i = 0
        while i < n:
            # 寻找潜在的稳态区间起点
            if i + min_length > n:
                break
            
            # 检查从当前位置开始的窗口
            start = i
            end = i + min_length - 1
            
            # 尝试扩展区间
            while end < n - 1:
                # 检查当前窗口是否满足稳态条件
                window_data = data[start:end+1]
                mean_val = np.mean(window_data)
                max_val = np.max(window_data)
                min_val = np.min(window_data)
                
                # 计算相对波动和绝对波动
                if abs(mean_val) > 1e-10:
                    relative_variation = (max_val - min_val) / abs(mean_val)
                else:
                    relative_variation = 0
                
                absolute_variation = max_val - min_val
                
                # 检查是否满足阈值条件
                if relative_variation <= threshold and absolute_variation <= abs_threshold:
                    # 尝试扩展一个点
                    test_window = data[start:end+2]
                    test_mean = np.mean(test_window)
                    test_max = np.max(test_window)
                    test_min = np.min(test_window)
                    
                    if abs(test_mean) > 1e-10:
                        test_relative = (test_max - test_min) / abs(test_mean)
                    else:
                        test_relative = 0
                    
                    test_absolute = test_max - test_min
                    
                    if test_relative <= threshold and test_absolute <= abs_threshold:
                        end += 1
                    else:
                        break
                else:
                    break
            
            # 检查区间长度是否满足最小要求
            interval_length = end - start + 1
            if interval_length >= min_length:
                # 如果启用了边界缩减
                if reduce_interval:
                    reduced_start, reduced_end = self.reduce_interval_boundaries(
                        data, start, end, threshold, abs_threshold
                    )
                    if reduced_end - reduced_start + 1 >= min_length:
                        intervals.append((reduced_start, reduced_end))
                        i = reduced_end + 1
                    else:
                        i += 1
                else:
                    intervals.append((start, end))
                    i = end + 1
            else:
                i += 1
        
        return intervals

    def reduce_interval_boundaries(self, data, start, end, threshold, abs_threshold):
        """缩减区间边界以获得更紧密的稳态区间 - 使用与copy3相同的算法"""
        if end <= start:
            return start, end
        
        window_data = data[start:end+1]
        mean_val = np.mean(window_data)
        
        # 计算每个点到均值的偏差
        deviations = []
        for val in window_data:
            if abs(mean_val) > 1e-10:
                rel_dev = abs(val - mean_val) / abs(mean_val)
            else:
                rel_dev = 0
            abs_dev = abs(val - mean_val)
            deviations.append((rel_dev, abs_dev))
        
        # 从起点开始缩减 - 找到第一个偏差较小的点
        new_start = start
        for i in range(len(deviations)):
            rel_dev, abs_dev = deviations[i]
            if rel_dev <= threshold * 0.5 and abs_dev <= abs_threshold * 0.5:
                new_start = start + i
                break
        
        # 从终点开始缩减 - 找到最后一个偏差较小的点
        new_end = end
        for i in range(len(deviations) - 1, -1, -1):
            rel_dev, abs_dev = deviations[i]
            if rel_dev <= threshold * 0.5 and abs_dev <= abs_threshold * 0.5:
                new_end = start + i
                break
        
        # 确保起点不大于终点
        if new_start > new_end:
            new_start = start
            new_end = end
        
        return new_start, new_end

    def plot_actual_load_data(self):
        """绘制实际负载数据和稳态区间"""
        # 先清除旧的分割点绘制对象（如果存在）
        if hasattr(self, 'segment_lines'):
            for line in self.segment_lines:
                try:
                    line.remove()
                except:
                    pass
        if hasattr(self, 'segment_texts'):
            for text in self.segment_texts:
                try:
                    text.remove()
                except:
                    pass
        
        self.ax_actual_load.clear()
        
        if not self.actual_load_data:
            self.canvas_actual_load.draw()
            return
        
        current_data = self.get_current_data()
        
        # 使用 x 位置而不是简单的索引
        if hasattr(self, 'actual_load_x_positions') and self.actual_load_x_positions:
            x_values = self.actual_load_x_positions
        else:
            x_values = list(range(len(current_data)))
        
        # 绘制数据曲线
        if self.is_filtered and self.filtered_data is not None:
            original_data = self.actual_load_data
            self.ax_actual_load.plot(x_values, original_data, color='#90caf9', alpha=0.5, linewidth=0.8, label='原始数据')
            self.ax_actual_load.plot(x_values, current_data, color='#f44336', linewidth=2.0, label='滤波数据', alpha=0.85)
        else:
            self.ax_actual_load.plot(x_values, current_data, color='#2196F3', linewidth=1.8, label='数据曲线', alpha=0.9)
        
        # 绘制稳态区间
        if self.current_intervals:
            for idx, (start, end) in enumerate(self.current_intervals):
                if start < len(current_data) and end < len(current_data):
                    interval_x = x_values[start:end+1]
                    interval_y = current_data[start:end+1] if isinstance(current_data, list) else current_data[start:end+1].tolist()
                    self.ax_actual_load.plot(interval_x, interval_y, color='#66bb6a', linewidth=2.5, alpha=0.7)
        
        # 设置标题和标签
        ylabel = '电流 (A)'
        title = '负载电流数据'
        
        self.ax_actual_load.set_xlabel('程序行号位置', fontsize=10)
        self.ax_actual_load.set_ylabel(ylabel, fontsize=10)
        self.ax_actual_load.set_title(title, fontsize=12, fontweight='bold')
        self.ax_actual_load.legend(loc='best', fontsize=9)
        if hasattr(self, 'actual_load_unique_line_numbers') and self.actual_load_unique_line_numbers:
            self.set_xticks_for_line_numbers()
        self.ax_actual_load.grid(True, alpha=0.3, linestyle='--')
        
        # 保存原始视图限制
        self.original_xlim = self.ax_actual_load.get_xlim()
        self.original_ylim = self.ax_actual_load.get_ylim()
        
        self.canvas_actual_load.draw()
        
        # 绑定滚轮缩放事件
        if not self.scroll_cid:
            self.bind_scroll_zoom()

    def get_original_data(self):
        """获取原始数据（未滤波）"""
        return self.actual_load_data

    def display_actual_load_results(self):
        """显示稳态区间分析结果 - 使用与copy3相同的显示格式"""
        self.actual_load_result_text.delete(1.0, tk.END)
        
        if not self.current_intervals:
            self.actual_load_result_text.insert(tk.END, "未识别到稳态区间\n")
            return
        
        current_data = self.get_current_data()
        
        result_text = f"识别到 {len(self.current_intervals)} 个稳态区间:\n"
        result_text += "=" * 60 + "\n\n"
        
        for idx, (start, end) in enumerate(self.current_intervals):
            if start >= len(current_data) or end >= len(current_data):
                continue
            
            interval_data = current_data[start:end+1]
            avg_value = np.mean(interval_data)
            std_value = np.std(interval_data)
            min_value = np.min(interval_data)
            max_value = np.max(interval_data)
            length = end - start + 1
            
            # 计算变异系数
            cv = (std_value / avg_value * 100) if avg_value != 0 else 0
            
            result_text += f"区间 {idx+1}:\n"
            result_text += f"  位置: [{start}, {end}]  长度: {length} 点\n"
            result_text += f"  平均值: {avg_value:.6f}\n"
            result_text += f"  标准差: {std_value:.6f}\n"
            result_text += f"  变异系数: {cv:.3f}%\n"
            result_text += f"  范围: [{min_value:.6f}, {max_value:.6f}]\n"
            result_text += "-" * 60 + "\n\n"
        
        self.actual_load_result_text.insert(tk.END, result_text)

    def save_analyzed_results_to_global(self):
        """将当前分析结果保存到全局字典（已废弃，使用collect_current_program_results代替）"""
        # 此函数已不再使用，保留仅为兼容性
        # 实际使用collect_current_program_results函数
        pass
    
    def collect_current_program_results(self):
        """收集当前程序和刀具的分析结果到全局字典"""
        if not hasattr(self, 'current_program_id') or not self.current_program_id:
            return
        
        if not hasattr(self, 'programs_data') or self.current_program_id not in self.programs_data:
            return
        
        # 检查是否有刀具信息
        if not hasattr(self, 'current_tool_key') or not self.current_tool_key:
            # 兼容旧版本 - 没有刀具key的情况不应该在新版本中保存
            return
        
        # 新版本：使用刀具级别数据
        if self.current_tool_key not in self.programs_data[self.current_program_id]:
            return
        prog_data = self.programs_data[self.current_program_id][self.current_tool_key]
        program_name = prog_data['name']
        tool_id = prog_data['tool_id']
        
        # 获取数据用于计算平均值
        current_data = None
        if 'filtered_data' in prog_data and prog_data['filtered_data'] is not None:
            current_data = prog_data['filtered_data']
        elif 'data' in prog_data:
            current_data = prog_data['data']
        
        # 收集所有区间(作为索引对)
        all_intervals_indices = []
        
        # 检查是否有分段数据
        if hasattr(self, 'segments') and self.segments:
            # 收集所有分段的区间
            for segment in self.segments:
                if 'intervals' in segment and segment['intervals']:
                    # 分段的intervals已经是全局索引
                    for start_idx, end_idx in segment['intervals']:
                        if (start_idx < len(self.actual_load_line_numbers) and 
                            end_idx < len(self.actual_load_line_numbers)):
                            all_intervals_indices.append((start_idx, end_idx))
        
        # 如果没有分段区间，使用整体区间
        if not all_intervals_indices and hasattr(self, 'actual_load_intervals') and self.actual_load_intervals:
            for start_idx, end_idx in self.actual_load_intervals:
                if (start_idx < len(self.actual_load_line_numbers) and 
                    end_idx < len(self.actual_load_line_numbers)):
                    all_intervals_indices.append((start_idx, end_idx))
        
        if not all_intervals_indices:
            return
        
        # 按起始索引排序
        all_intervals_indices.sort(key=lambda x: x[0])
        
        # 合并相邻且连续的区间
        merged_intervals_indices = []
        current_start, current_end = all_intervals_indices[0]
        
        for i in range(1, len(all_intervals_indices)):
            next_start, next_end = all_intervals_indices[i]
            
            # 检查是否连续(允许1个点的间隙)
            if next_start <= current_end + 1:
                # 合并区间
                current_end = max(current_end, next_end)
            else:
                # 保存当前区间,开始新区间
                merged_intervals_indices.append((current_start, current_end))
                current_start, current_end = next_start, next_end
        
        # 添加最后一个区间
        merged_intervals_indices.append((current_start, current_end))
        
        # 计算区间平均值和动态理想值（使用与界面显示一致的方法）
        interval_averages = []  # 每个区间的平均值（用于保存到rg文件的区间平均值字段）
        all_interval_data_points = []  # 所有区间内的数据点（用于计算整体理想值）
        
        if current_data is not None:
            for start_idx, end_idx in merged_intervals_indices:
                if start_idx < len(current_data) and end_idx < len(current_data):
                    # 切片包含end_idx
                    slice_data = current_data[start_idx:end_idx+1]
                    if len(slice_data) > 0:
                        interval_averages.append(np.mean(slice_data))
                        # 收集所有区间内的数据点
                        all_interval_data_points.extend(slice_data)
                    else:
                        interval_averages.append(0)
                else:
                    interval_averages.append(0)
        
        # 计算动态理想值: (所有区间内数据点的平均值) * 调整倍率
        # 这样与界面显示的 calculate_interval_average() 方法保持一致
        # 获取调整倍率
        try:
            ratio = prog_data.get('adjustment_ratio', 1.2)
        except:
            ratio = 1.2
        
        if all_interval_data_points:
            # 使用所有区间内数据点的平均值（与界面显示一致）
            base_avg = np.mean(all_interval_data_points)
            ideal_value = base_avg * ratio
        else:
            # 回退到整体平均值
            ideal_value = prog_data.get('average', 0) * ratio

        # 转换为行号.点索引格式
        intervals_list = []
        for i, (start_idx, end_idx) in enumerate(merged_intervals_indices):
            if (start_idx < len(self.actual_load_x_positions) and
                end_idx < len(self.actual_load_x_positions)):
                
                # 使用x_positions获取准确的位置（行号+点索引/该行总点数）
                start_pos = self.actual_load_x_positions[start_idx]
                end_pos = self.actual_load_x_positions[end_idx]
                
                # 分离整数部分（行号）和小数部分（相对位置）
                start_ln = int(start_pos)
                start_frac = start_pos - start_ln
                end_ln = int(end_pos)
                end_frac = end_pos - end_ln
                
                # 获取实际的点索引
                start_point = self.actual_load_point_indices[start_idx]
                end_point = self.actual_load_point_indices[end_idx]
                
                # 获取该区间的平均值
                this_interval_avg = interval_averages[i] if i < len(interval_averages) else 0

                intervals_list.append((f"{start_ln}.{start_point}", 
                                     f"{end_ln}.{end_point}", 
                                     ideal_value,
                                     this_interval_avg))
        
        # 只有当有区间时才保存
        if intervals_list:
            # 使用 (program_id, tool_key) 作为键，保持txt文件中的完整顺序
            # 这样可以支持同一程序的多个刀具，包括重复的刀具号
            result_key = (self.current_program_id, self.current_tool_key)
            
            # 保存结果，包含程序名、刀具ID等信息
            self.analyzed_results[result_key] = {
                'program_id': self.current_program_id,
                'program_name': program_name,
                'tool_id': prog_data['tool_id'],
                'tool_key': self.current_tool_key,
                'intervals': intervals_list
            }
    
    def save_actual_load_results(self):
        """保存实际负载分析结果"""
        # 先保存当前程序和刀具的状态和结果
        if hasattr(self, 'current_program_id') and self.current_program_id:
            self.save_current_program_state()
        self.collect_current_program_results()
        
        # 遍历所有已分析的程序和刀具，确保都收集到analyzed_results中
        saved_current_prog_id = getattr(self, 'current_program_id', None)
        saved_current_tool_key = getattr(self, 'current_tool_key', None)
        
        for program_id, prog_data_or_tools in self.programs_data.items():
            # 检查是否是新格式（包含刀具）
            if isinstance(prog_data_or_tools, dict):
                # 检查是否有刀具数据
                has_tools = False
                for key, value in prog_data_or_tools.items():
                    if isinstance(value, dict) and 'tool_key' in value:
                        has_tools = True
                        break
                
                if has_tools:
                    # 新格式：遍历所有刀具
                    for tool_key, tool_data in prog_data_or_tools.items():
                        if isinstance(tool_data, dict) and 'intervals' in tool_data and tool_data['intervals']:
                            # 临时切换到该程序和刀具以收集结果
                            self.current_program_id = program_id
                            self.current_tool_key = tool_key
                            self.actual_load_intervals = tool_data['intervals']
                            self.actual_load_line_numbers = tool_data['line_numbers']
                            self.actual_load_point_indices = tool_data['point_indices']
                            self.actual_load_x_positions = tool_data.get('x_positions', tool_data['line_numbers'])
                            self.collect_current_program_results()
                else:
                    # 旧格式：没有刀具
                    if 'intervals' in prog_data_or_tools and prog_data_or_tools['intervals']:
                        self.current_program_id = program_id
                        self.current_tool_key = None
                        self.actual_load_intervals = prog_data_or_tools['intervals']
                        self.actual_load_line_numbers = prog_data_or_tools['line_numbers']
                        self.actual_load_point_indices = prog_data_or_tools['point_indices']
                        self.actual_load_x_positions = prog_data_or_tools.get('x_positions', prog_data_or_tools['line_numbers'])
                        self.collect_current_program_results()
        
        # 恢复当前程序和刀具key
        self.current_program_id = saved_current_prog_id
        self.current_tool_key = saved_current_tool_key
        
        if not hasattr(self, 'analyzed_results') or not self.analyzed_results:
            messagebox.showwarning("无结果", "没有已分析的结果，请先运行分析")
            return
        try:
            # 获取程序所在目录
            import sys
            if getattr(sys, 'frozen', False):
                # 打包后的exe环境
                save_dir = os.path.dirname(sys.executable)
            else:
                # 开发环境
                save_dir = os.path.dirname(os.path.abspath(__file__))
            
            # 保存汇总结果，修改为SampleData.rg
            summary_path = os.path.join(save_dir, "SampleData.rg")
            
            # 获取数据源标识（0=电流，1=vgpro功率，2=边缘模块功率）
            data_source_map = {'电流': 0, 'vgpro功率': 1, '边缘模块功率': 2}
            data_source_id = data_source_map.get(self.data_source.get(), 0)
            
            # 调试信息：打印analyzed_results的键
            print(f"=== 调试信息 ===")
            print(f"analyzed_results包含的键:")
            for key in self.analyzed_results.keys():
                print(f"  {key}")
            print(f"program_mapping包含的程序:")
            for prog_id, prog_info in self.program_mapping.items():
                print(f"  程序ID: {prog_id}, 名称: {prog_info['name']}, 刀具数: {len(prog_info.get('tools_list', []))}")
            
            # 按照txt文件顺序整理结果
            # 格式: [(program_id, tool_key, program_name, tool_id, ideal_value, intervals), ...]
            ordered_results = []
            
            # 遍历program_mapping以保持txt文件顺序
            for program_id, program_info in self.program_mapping.items():
                tools_list = program_info.get('tools_list', [])
                
                # 遍历每个刀具(按txt顺序,包括重复的刀具)
                for tool_index, tool_info in enumerate(tools_list):
                    tool_id = tool_info['tool_id']
                    tool_key = f"{tool_id}_{tool_index}"
                    result_key = (program_id, tool_key)
                    
                    # 检查是否有该刀具的分析结果
                    if result_key in self.analyzed_results:
                        print(f"找到结果: 程序ID={program_id}, 刀具key={tool_key}")
                    else:
                        print(f"未找到结果: 程序ID={program_id}, 刀具key={tool_key}")
                    
                    if result_key in self.analyzed_results:
                        result_data = self.analyzed_results[result_key]
                        intervals_list = result_data['intervals']
                        program_name = result_data['program_name']
                        
                        # 按理想值分组该刀具的区间
                        ideal_groups = {}  # {ideal_value: [intervals]}
                        for start_str, end_str, ideal_value, interval_avg in intervals_list:
                            ideal_key = f"{ideal_value:.3f}"
                            if ideal_key not in ideal_groups:
                                ideal_groups[ideal_key] = []
                            # 修改格式：区间起始-区间终止:区间平均值
                            interval_str = f"{start_str}-{end_str}:{interval_avg:.3f}"
                            ideal_groups[ideal_key].append(interval_str)
                        
                        # 将该刀具的每个理想值组添加到结果列表
                        for ideal_key, intervals in ideal_groups.items():
                            print(f"添加到ordered_results: {program_name}, {tool_id}, 理想值={ideal_key}, 区间数={len(intervals)}")
                            ordered_results.append({
                                'program_name': program_name,
                                'tool_id': tool_id,
                                'ideal_value': ideal_key,
                                'intervals': intervals
                            })
            
            print(f"ordered_results总数: {len(ordered_results)}")
            print(f"=== 调试信息结束 ===")
            
            # 写入文件
            with open(summary_path, 'w', encoding='utf-8') as f:
                # 第一行：数据源标识
                f.write(f"{data_source_id}\n")
                
                # 按照ordered_results的顺序写入(已按txt顺序排列)
                for result in ordered_results:
                    program_name = result['program_name']
                    ideal_value_str = result['ideal_value']
                    intervals = result['intervals']
                    
                    # 按起始行号排序区间
                    def get_start_position(interval_str):
                        # 解析 "起始行号.点索引-结束行号.点索引" 格式
                        start_part = interval_str.split('-')[0]
                        parts = start_part.split('.')
                        line_num = float(parts[0])
                        point_idx = float(parts[1]) if len(parts) > 1 else 0
                        # 返回完整的位置值用于排序
                        return line_num + point_idx / 10000.0  # 使用足够小的权重
                    
                    intervals_sorted = sorted(intervals, key=get_start_position)
                    
                    # 将区间用逗号连接
                    intervals_str = ','.join(intervals_sorted)
                    
                    # 格式: 程序名;理想值;区间1起始-区间1终止,区间2起始-区间2终止;
                    f.write(f"{program_name};{ideal_value_str};{intervals_str};\n")

            # 同时生成一个只包含所有区间真实平均值的 CSV 文件（每行一个平均值）
            test_csv_path = os.path.join(save_dir, "test.csv")
            try:
                with open(test_csv_path, 'w', encoding='utf-8', newline='') as tf:
                    # 遍历 analyzed_results，解析每个区间的起止位置并计算区间内数据的平均值
                    for res_key, res_data in self.analyzed_results.items():
                        program_id, tool_key = res_key
                        intervals = res_data.get('intervals', [])

                        # 尝试从 programs_data 中获取对应的数组（优先使用滤波数据 if available）
                        prog_tool_data = None
                        try:
                            prog_tool_data = self.programs_data.get(program_id, {}).get(tool_key)
                        except Exception:
                            prog_tool_data = None

                        for start_str, end_str, ideal_value, _ in intervals:
                            avg_to_write = None
                            # 解析 start_str/end_str 格式为 "行号.点索引"
                            try:
                                s_parts = str(start_str).split('.')
                                e_parts = str(end_str).split('.')
                                s_line = float(s_parts[0])
                                s_point = int(s_parts[1]) if len(s_parts) > 1 else 0
                                e_line = float(e_parts[0])
                                e_point = int(e_parts[1]) if len(e_parts) > 1 else 0

                                if prog_tool_data is not None:
                                    # 获取索引数组
                                    line_nums = np.asarray(prog_tool_data.get('line_numbers'))
                                    point_idxs = np.asarray(prog_tool_data.get('point_indices'))

                                    # 找到起始与结束索引（取第一个匹配项）
                                    start_idx_candidates = np.where((line_nums == s_line) & (point_idxs == s_point))[0]
                                    end_idx_candidates = np.where((line_nums == e_line) & (point_idxs == e_point))[0]

                                    if start_idx_candidates.size > 0 and end_idx_candidates.size > 0:
                                        start_idx = int(start_idx_candidates[0])
                                        end_idx = int(end_idx_candidates[-1])

                                        # 保证索引顺序
                                        if end_idx < start_idx:
                                            start_idx, end_idx = end_idx, start_idx

                                        # 取数据（优先使用滤波数据 if present and length matches）
                                        if prog_tool_data.get('is_filtered') and prog_tool_data.get('filtered_data') is not None:
                                            data_array = np.asarray(prog_tool_data.get('filtered_data'))
                                        else:
                                            data_array = np.asarray(prog_tool_data.get('data'))

                                        # 防越界检查
                                        if 0 <= start_idx < len(data_array) and 0 <= end_idx < len(data_array) and end_idx >= start_idx:
                                            interval_vals = data_array[start_idx:end_idx+1]
                                            if len(interval_vals) > 0:
                                                avg_to_write = float(np.mean(interval_vals))
                            except Exception as e:
                                # 解析或计算时出错，后面回退到理想值
                                avg_to_write = None

                            # 回退：如果无法计算真实平均值，则使用保存的 ideal_value
                            if avg_to_write is None:
                                try:
                                    avg_to_write = float(ideal_value)
                                except Exception:
                                    avg_to_write = 0.0

                            tf.write(f"{avg_to_write}\n")
            except Exception as e:
                # 记录错误但不阻止主保存流程
                print(f"写入 test.csv 时出错: {e}")

            self.status_var_actual_load.set(f"结果已保存到: {save_dir}")
            
            # 统计信息
            total_programs = len(set(r['program_name'] for r in ordered_results))
            total_intervals = sum(len(r['intervals']) for r in ordered_results)
            
            # 列出所有已保存的程序名(去重)
            unique_programs = sorted(set(r['program_name'] for r in ordered_results))
            program_names_str = "\n".join([f"  • {name}" for name in unique_programs])
            
            # 数据源名称
            data_source_name = self.data_source.get()
            
            messagebox.showinfo("保存成功", 
                            f"✓ 已保存 {total_programs} 个程序的分析结果\n" +
                            f"✓ 共 {total_intervals} 个稳态区间（已自动合并连续区间）\n" +
                            f"✓ 数据源: {data_source_name} (标识: {data_source_id})\n\n" +
                            f"已保存的程序:\n{program_names_str}\n\n" +
                            f"保存位置: {save_dir}\n" +
                            f"文件名: SampleData.rg")
            
            self.status_var_actual_load.set(f"成功保存 {total_programs} 个程序，共 {total_intervals} 个区间")
                            
        except Exception as e:
            messagebox.showerror("保存错误", f"保存结果时发生错误:\n{str(e)}")

    def bind_scroll_zoom(self):
        """绑定鼠标滚轮缩放功能"""
        if self.scroll_cid:
            self.canvas_actual_load.mpl_disconnect(self.scroll_cid)
        
        self.scroll_cid = self.canvas_actual_load.mpl_connect('scroll_event', self.on_scroll_zoom)

    def on_scroll_zoom(self, event):
        """处理鼠标滚轮缩放事件（仅横向缩放）"""
        if event.inaxes != self.ax_actual_load:
            return
        
        # 获取当前X轴和Y轴的范围
        cur_xlim = self.ax_actual_load.get_xlim()
        cur_ylim = self.ax_actual_load.get_ylim()
        
        # 获取鼠标在数据坐标中的位置
        xdata = event.xdata
        ydata = event.ydata
        
        if xdata is None or ydata is None:
            return
        
        # 根据滚轮方向确定缩放方向
        if event.button == 'up':
            # 放大
            scale_factor = 1 / self.zoom_factor
        elif event.button == 'down':
            # 缩小
            scale_factor = self.zoom_factor
        else:
            return
        
        # 只计算横向（X轴）的新范围，以鼠标位置为中心缩放
        new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
        
        relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0])
        
        new_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
        
        # 应用新的X轴范围，Y轴保持不变
        self.ax_actual_load.set_xlim(new_xlim)
        self.ax_actual_load.set_ylim(cur_ylim)  # 保持Y轴范围不变
        
        # 重绘图表
        self.canvas_actual_load.draw()

    def reset_chart_view(self):
        """重置图表视图到原始范围"""
        if self.original_xlim is not None and self.original_ylim is not None:
            self.ax_actual_load.set_xlim(self.original_xlim)
            self.ax_actual_load.set_ylim(self.original_ylim)
            self.canvas_actual_load.draw()
            self.status_var_actual_load.set("图表视图已重置")
    
    def on_pan_press(self, event):
        """处理鼠标按下事件（开始平移）"""
        # 只响应鼠标左键，且在图表区域内
        if event.button != 1 or event.inaxes != self.ax_actual_load:
            return
        
        # 记录起始位置
        self.is_panning = True
        self.pan_start = (event.xdata, event.ydata)
    
    def on_pan_motion(self, event):
        """处理鼠标移动事件（执行平移）- 只影响横轴"""
        # 如果不在平移状态，或者鼠标不在图表区域内，则返回
        if not self.is_panning or event.inaxes != self.ax_actual_load or self.pan_start is None:
            return
        
        # 如果鼠标数据坐标为None，则返回
        if event.xdata is None or event.ydata is None:
            return
        
        # 计算鼠标在X轴方向的移动距离
        dx = event.xdata - self.pan_start[0]
        
        # 获取当前坐标轴范围
        cur_xlim = self.ax_actual_load.get_xlim()
        cur_ylim = self.ax_actual_load.get_ylim()
        
        # 只更新X轴范围（反向移动，实现拖动效果），Y轴保持不变
        new_xlim = [cur_xlim[0] - dx, cur_xlim[1] - dx]
        
        # 应用新的X轴范围，Y轴保持不变
        self.ax_actual_load.set_xlim(new_xlim)
        self.ax_actual_load.set_ylim(cur_ylim)
        
        # 重绘图表
        self.canvas_actual_load.draw()

    def on_pan_release(self, event):
        """处理鼠标释放事件（结束平移）"""
        self.is_panning = False
        self.pan_start = None

    def on_window_resize(self, event):
        """窗口大小改变时的处理"""
        if event.widget == self.root:
            self.root.after(100, self.adjust_figure_size)
    
    def toggle_adjustment_mode(self):
        """切换微调模式"""
        self.adjustment_mode = not self.adjustment_mode

        if self.adjustment_mode:
            # 进入微调模式
            self.adjustment_button.config(text="✓ 微调中")
            self.enable_adjustment_mode()
            self.status_var_actual_load.set(
                "微调模式：左键拖动区间边界调整，右键点击区间删除，Ctrl+左键选择多个区间后点击'合并'"
            )
        else:
            # 退出微调模式
            self.adjustment_button.config(text="✏️ 微调")
            self.disable_adjustment_mode()
            self.status_var_actual_load.set("已退出微调模式")

    def enable_adjustment_mode(self):
        """启用微调模式"""
        # 断开平移事件，但保留滚动缩放功能
        if hasattr(self, 'press_cid') and self.press_cid:
            self.canvas_actual_load.mpl_disconnect(self.press_cid)
            self.press_cid = None
        if hasattr(self, 'motion_cid') and self.motion_cid:
            self.canvas_actual_load.mpl_disconnect(self.motion_cid)
            self.motion_cid = None
        if hasattr(self, 'release_cid') and self.release_cid:
            self.canvas_actual_load.mpl_disconnect(self.release_cid)
            self.release_cid = None
        
        # 保留滚动缩放功能（不断开 scroll_cid）

        # 连接微调模式的事件
        self.adjustment_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_adjustment_press)
        self.adjustment_motion_cid = self.canvas_actual_load.mpl_connect('motion_notify_event', self.on_adjustment_motion)
        self.adjustment_release_cid = self.canvas_actual_load.mpl_connect('button_release_event', self.on_adjustment_release)

        # 绘制可调整的边界线
        self.draw_interval_boundaries()

    def disable_adjustment_mode(self):
        """禁用微调模式"""
        # 断开微调模式的事件
        if self.adjustment_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_cid)
            self.adjustment_cid = None
        if self.adjustment_motion_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_motion_cid)
            self.adjustment_motion_cid = None
        if self.adjustment_release_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_release_cid)
            self.adjustment_release_cid = None

        # 清除边界线和选中标记
        self.clear_interval_boundaries()
        self.selected_intervals = []

        # 恢复正常的交互事件
        self.press_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_pan_press)
        self.motion_cid = self.canvas_actual_load.mpl_connect('motion_notify_event', self.on_pan_motion)
        self.release_cid = self.canvas_actual_load.mpl_connect('button_release_event', self.on_pan_release)

        # 保存当前状态并刷新刀具选择器显示（保持当前选择）
        self.save_current_program_state()
        if hasattr(self, 'current_program_id') and self.current_program_id:
            self.update_tool_selector(self.current_program_id, preserve_selection=True)

        # 重新绘制图表
        self.canvas_actual_load.draw()

    def bind_scroll_zoom(self):
        """绑定鼠标滚轮缩放功能"""
        if self.scroll_cid:
            self.canvas_actual_load.mpl_disconnect(self.scroll_cid)
        
        self.scroll_cid = self.canvas_actual_load.mpl_connect('scroll_event', self.on_scroll_zoom)

    def on_scroll_zoom(self, event):
        """处理鼠标滚轮缩放事件（仅横向缩放）"""
        if event.inaxes != self.ax_actual_load:
            return
        
        # 获取当前坐标轴范围
        cur_xlim = self.ax_actual_load.get_xlim()
        cur_ylim = self.ax_actual_load.get_ylim()
        
        # 获取鼠标在数据坐标中的位置
        xdata = event.xdata
        ydata = event.ydata
        
        if xdata is None or ydata is None:
            return
        
        # 根据滚轮方向确定缩放方向
        if event.button == 'up':
            # 放大
            scale_factor = 1 / self.zoom_factor
        elif event.button == 'down':
            # 缩小
            scale_factor = self.zoom_factor
        else:
            return
        
        # 只计算横向（X轴）的新范围，以鼠标位置为中心缩放
        new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
        
        relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0])
        
        new_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
        
        # 应用新的X轴范围，Y轴保持不变
        self.ax_actual_load.set_xlim(new_xlim)
        self.ax_actual_load.set_ylim(cur_ylim)  # 保持Y轴范围不变
        
        # 重绘图表
        self.canvas_actual_load.draw()

    def reset_chart_view(self):
        """重置图表视图到原始范围"""
        if self.original_xlim is not None and self.original_ylim is not None:
            self.ax_actual_load.set_xlim(self.original_xlim)
            self.ax_actual_load.set_ylim(self.original_ylim)
            self.canvas_actual_load.draw()
            self.status_var_actual_load.set("图表视图已重置")
    
    def on_pan_press(self, event):
        """处理鼠标按下事件（开始平移）"""
        # 只响应鼠标左键，且在图表区域内
        if event.button != 1 or event.inaxes != self.ax_actual_load:
            return
        
        # 记录起始位置
        self.is_panning = True
        self.pan_start = (event.xdata, event.ydata)
    
    def on_pan_release(self, event):
        """处理鼠标释放事件（结束平移）"""
        self.is_panning = False
        self.pan_start = None
    
    def on_pan_motion(self, event):
        """处理鼠标移动事件（执行平移）- 只影响横轴"""
        # 如果不在平移状态，或者鼠标不在图表区域内，则返回
        if not self.is_panning or event.inaxes != self.ax_actual_load or self.pan_start is None:
            return
        
        # 如果鼠标数据坐标为None，则返回
        if event.xdata is None or event.ydata is None:
            return
        
        # 计算鼠标在X轴方向的移动距离
        dx = event.xdata - self.pan_start[0]
        
        # 获取当前坐标轴范围
        cur_xlim = self.ax_actual_load.get_xlim()
        cur_ylim = self.ax_actual_load.get_ylim()
        
        # 只更新X轴范围（反向移动，实现拖动效果），Y轴保持不变
        new_xlim = [cur_xlim[0] - dx, cur_xlim[1] - dx]
        
        # 应用新的X轴范围，Y轴保持不变
        self.ax_actual_load.set_xlim(new_xlim)
        self.ax_actual_load.set_ylim(cur_ylim)
        
        # 重绘图表
        self.canvas_actual_load.draw()

    def on_window_resize(self, event):
        """窗口大小改变时的处理"""
        if event.widget == self.root:
            self.root.after(100, self.adjust_figure_size)
    
    def toggle_adjustment_mode(self):
        """切换微调模式"""
        self.adjustment_mode = not self.adjustment_mode

        if self.adjustment_mode:
            # 进入微调模式
            self.adjustment_button.config(text="✓ 微调中")
            self.enable_adjustment_mode()
            self.status_var_actual_load.set(
                "微调模式：左键拖动区间边界调整，右键点击区间删除，Ctrl+左键选择多个区间后点击'合并'"
            )
        else:
            # 退出微调模式
            self.adjustment_button.config(text="✏️ 微调")
            self.disable_adjustment_mode()
            self.status_var_actual_load.set("已退出微调模式")

    def enable_adjustment_mode(self):
        """启用微调模式"""
        # 断开平移事件，但保留滚动缩放功能
        if hasattr(self, 'press_cid') and self.press_cid:
            self.canvas_actual_load.mpl_disconnect(self.press_cid)
            self.press_cid = None
        if hasattr(self, 'motion_cid') and self.motion_cid:
            self.canvas_actual_load.mpl_disconnect(self.motion_cid)
            self.motion_cid = None
        if hasattr(self, 'release_cid') and self.release_cid:
            self.canvas_actual_load.mpl_disconnect(self.release_cid)
            self.release_cid = None
        
        # 保留滚动缩放功能（不断开 scroll_cid）

        # 连接微调模式的事件
        self.adjustment_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_adjustment_press)
        self.adjustment_motion_cid = self.canvas_actual_load.mpl_connect('motion_notify_event', self.on_adjustment_motion)
        self.adjustment_release_cid = self.canvas_actual_load.mpl_connect('button_release_event', self.on_adjustment_release)

        # 绘制可调整的边界线
        self.draw_interval_boundaries()

    def disable_adjustment_mode(self):
        """禁用微调模式"""
        # 断开微调模式的事件
        if self.adjustment_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_cid)
            self.adjustment_cid = None
        if self.adjustment_motion_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_motion_cid)
            self.adjustment_motion_cid = None
        if self.adjustment_release_cid:
            self.canvas_actual_load.mpl_disconnect(self.adjustment_release_cid)
            self.adjustment_release_cid = None

        # 清除边界线和选中标记
        self.clear_interval_boundaries()
        self.selected_intervals = []

        # 恢复正常的交互事件
        self.press_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_pan_press)
        self.motion_cid = self.canvas_actual_load.mpl_connect('motion_notify_event', self.on_pan_motion)
        self.release_cid = self.canvas_actual_load.mpl_connect('button_release_event', self.on_pan_release)

        # 重新绘制图表
        self.canvas_actual_load.draw()

    def draw_interval_boundaries(self):
        """绘制区间边界线（可拖动）"""
        # 保存当前视图范围
        current_xlim = self.ax_actual_load.get_xlim()
        current_ylim = self.ax_actual_load.get_ylim()
        
        self.clear_interval_boundaries()

        if not self.actual_load_intervals:
            return

        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            if start_idx >= len(self.actual_load_x_positions) or end_idx >= len(self.actual_load_x_positions):
                continue

            start_x = self.actual_load_x_positions[start_idx]
            end_x = self.actual_load_x_positions[end_idx]

            # 绘制起始边界线（红色）
            start_line = self.ax_actual_load.axvline(
                x=start_x,
                color='red',
                linewidth=2.5,
                alpha=0.8,
                linestyle='-',
                picker=5,
            )
            start_line.interval_info = {'idx': i, 'boundary': 'start'}
            self.interval_boundary_lines.append(start_line)

            # 绘制结束边界线（蓝色）
            end_line = self.ax_actual_load.axvline(
                x=end_x,
                color='blue',
                linewidth=2.5,
                alpha=0.8,
                linestyle='-',
                picker=5,
            )
            end_line.interval_info = {'idx': i, 'boundary': 'end'}
            self.interval_boundary_lines.append(end_line)

        # 恢复之前的视图范围
        self.ax_actual_load.set_xlim(current_xlim)
        self.ax_actual_load.set_ylim(current_ylim)
        
        self.canvas_actual_load.draw()

    def clear_interval_boundaries(self):
        """清除区间边界线"""
        for line in self.interval_boundary_lines:
            try:
                line.remove()
            except:
                pass
        self.interval_boundary_lines = []

    def on_adjustment_press(self, event):
        """微调模式下的鼠标按下事件"""
        if event.inaxes != self.ax_actual_load:
            return

        if event.button == 1:  # 左键
            # 检查是否按下了Ctrl键（用于多选）
            # matplotlib 中 Ctrl 键的检测方式
            if event.key == 'control' or (hasattr(event, 'guiEvent') and hasattr(event.guiEvent, 'state') and event.guiEvent.state & 0x4):
                # 多选模式：选择区间
                self.select_interval_at_position(event.xdata)
            else:
                # 检查是否点击了边界线
                self.check_boundary_click(event)
        elif event.button == 3:  # 右键
            # 删除区间
            self.delete_interval_at_position(event.xdata)

    def on_adjustment_motion(self, event):
        """微调模式下的鼠标移动事件"""
        # 只有在正在拖动且鼠标左键按下时才处理
        if self.dragging_boundary and event.xdata is not None and event.button == 1:
            # 拖动边界线
            interval_idx = self.dragging_boundary['interval_idx']
            boundary = self.dragging_boundary['boundary']
            line = self.dragging_boundary['line']

            # 找到最接近鼠标位置的数据点索引
            closest_idx = np.argmin(np.abs(np.array(self.actual_load_x_positions) - event.xdata))

            # 获取当前区间
            start_idx, end_idx = self.actual_load_intervals[interval_idx]

            # 更新边界 - 移除限制，允许自由移动
            if boundary == 'start':
                start_idx = closest_idx
                new_x = self.actual_load_x_positions[closest_idx]
                line.set_xdata([new_x, new_x])
            else:  # 'end'
                end_idx = closest_idx
                new_x = self.actual_load_x_positions[closest_idx]
                line.set_xdata([new_x, new_x])

            # 更新区间数据（临时，释放鼠标时才确认）
            # 如果起始位置大于结束位置，交换它们
            if start_idx > end_idx:
                self.actual_load_intervals[interval_idx] = (end_idx, start_idx)
            else:
                self.actual_load_intervals[interval_idx] = (start_idx, end_idx)

            self.canvas_actual_load.draw()

    def on_adjustment_release(self, event):
        """微调模式下的鼠标释放事件"""
        if self.dragging_boundary:
            # 保存当前视图范围
            xlim = self.ax_actual_load.get_xlim()
            ylim = self.ax_actual_load.get_ylim()
            
            # 自动合并重叠或相邻的区间
            merged = self.auto_merge_overlapping_intervals()
            
            # 确认边界调整，保存到程序数据
            if self.current_program_id and self.current_tool_key:
                if self.current_program_id in self.programs_data:
                    if self.current_tool_key in self.programs_data[self.current_program_id]:
                        self.programs_data[self.current_program_id][self.current_tool_key]['intervals'] = self.actual_load_intervals.copy()
                    else:
                        # 兼容旧版本：如果没有tool_key，保存到程序级别
                        self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()
            elif self.current_program_id and self.current_program_id in self.programs_data:
                # 兼容旧版本：如果没有tool_key，保存到程序级别
                self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()

            # 直接重新绘制稳态区间图表，显示调整后的边界和更新的高亮区域
            # plot_steady_intervals 和 draw_interval_boundaries 都会自动保持视图范围
            data_type = "滤波" if self.is_filtered else "原始"
            self.plot_steady_intervals(data_type)
            self.draw_interval_boundaries()
            
            # 刷新区间详情和基准值，并保存状态
            self.refresh_interval_ui(data_type)
            
            # 刷新刀具选择器（保持当前选择）
            if hasattr(self, 'current_program_id') and self.current_program_id:
                self.update_tool_selector(self.current_program_id, preserve_selection=True)

            self.dragging_boundary = None
            if merged:
                self.status_var_actual_load.set(f"区间边界已调整，已自动合并 {merged} 组重叠区间")
            else:
                self.status_var_actual_load.set("区间边界已调整")

    def check_boundary_click(self, event):
        """检查是否点击了边界线"""
        if not self.actual_load_intervals or event.xdata is None:
            return

        # 计算容差（屏幕坐标的1%）
        xlim = self.ax_actual_load.get_xlim()
        tolerance = (xlim[1] - xlim[0]) * 0.01

        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            if start_idx >= len(self.actual_load_x_positions) or end_idx >= len(self.actual_load_x_positions):
                continue

            start_x = self.actual_load_x_positions[start_idx]
            end_x = self.actual_load_x_positions[end_idx]

            # 检查是否点击了起始边界
            if abs(event.xdata - start_x) < tolerance:
                # 找到对应的线对象
                for line in self.interval_boundary_lines:
                    if hasattr(line, 'interval_info') and line.interval_info['idx'] == i and line.interval_info['boundary'] == 'start':
                        self.dragging_boundary = {
                            'interval_idx': i,
                            'boundary': 'start',
                            'line': line,
                        }
                        self.status_var_actual_load.set(f"拖动区间{i+1}的起始边界")
                        return

            # 检查是否点击了结束边界
            if abs(event.xdata - end_x) < tolerance:
                # 找到对应的线对象
                for line in self.interval_boundary_lines:
                    if hasattr(line, 'interval_info') and line.interval_info['idx'] == i and line.interval_info['boundary'] == 'end':
                        self.dragging_boundary = {
                            'interval_idx': i,
                            'boundary': 'end',
                            'line': line,
                        }
                        self.status_var_actual_load.set(f"拖动区间{i+1}的结束边界")
                        return

    def select_interval_at_position(self, x_pos):
        """在指定位置选择区间（用于多选）"""
        if not self.actual_load_intervals or x_pos is None:
            return

        # 找到包含该位置的区间
        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            if start_idx >= len(self.actual_load_x_positions) or end_idx >= len(self.actual_load_x_positions):
                continue

            start_x = self.actual_load_x_positions[start_idx]
            end_x = self.actual_load_x_positions[end_idx]

            if start_x <= x_pos <= end_x:
                if i in self.selected_intervals:
                    # 取消选择
                    self.selected_intervals.remove(i)
                else:
                    # 添加选择
                    self.selected_intervals.append(i)

                # 高亮显示选中的区间
                self.highlight_selected_intervals()
                self.status_var_actual_load.set(f"已选择 {len(self.selected_intervals)} 个区间")
                return

    def highlight_selected_intervals(self):
        """高亮显示选中的区间"""
        # 保存当前视图范围
        xlim = self.ax_actual_load.get_xlim()
        ylim = self.ax_actual_load.get_ylim()
        
        # 重新绘制图表，但只改变选中区间的颜色
        self.ax_actual_load.clear()

        # 绘制数据曲线
        self.ax_actual_load.plot(
            self.actual_load_x_positions,
            self.actual_load_data,
            color='#2196F3',
            linewidth=1.8,
            label='负载电流值',
            alpha=0.9
        )

        if self.is_filtered and self.filtered_data is not None:
            self.ax_actual_load.plot(
                self.actual_load_x_positions,
                self.filtered_data,
                color='#f44336',
                linewidth=2.0,
                label='滤波后数据',
                alpha=0.85
            )

        # 绘制区间（选中的用不同颜色）
        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            if start_idx >= len(self.actual_load_x_positions) or end_idx >= len(self.actual_load_x_positions):
                continue

            start_x = self.actual_load_x_positions[start_idx]
            end_x = self.actual_load_x_positions[end_idx]

            if i in self.selected_intervals:
                # 选中的区间用黄色高亮
                self.ax_actual_load.axvspan(
                    start_x,
                    end_x,
                    alpha=0.4,
                    color='yellow',
                    edgecolor='orange',
                    linewidth=2.0,
                )
            else:
                # 未选中的区间用绿色
                self.ax_actual_load.axvspan(
                    start_x,
                    end_x,
                    alpha=0.3,
                    color='lightgreen',
                    edgecolor='darkgreen',
                    linewidth=1.0,
                )

            self.ax_actual_load.axvline(x=start_x, color='black', linewidth=0.5, alpha=0.8)
            self.ax_actual_load.axvline(x=end_x, color='black', linewidth=0.5, alpha=0.8)

        # 重新绘制边界线
        self.draw_interval_boundaries()

        # 设置标题和标签
        title = '负载电流稳态区间'
        ylabel = '电流 (A)'

        self.ax_actual_load.set_title(title)
        self.ax_actual_load.set_xlabel('程序行号位置')
        self.ax_actual_load.set_ylabel(ylabel)
        self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
        self.ax_actual_load.legend(loc='upper right')
        
        # 恢复视图范围
        self.ax_actual_load.set_xlim(xlim)
        self.ax_actual_load.set_ylim(ylim)

        self.canvas_actual_load.draw()

    def delete_interval_at_position(self, x_pos):
        """删除指定位置的区间"""
        if not self.actual_load_intervals or x_pos is None:
            return

        # 找到包含该位置的区间
        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            if start_idx >= len(self.actual_load_x_positions) or end_idx >= len(self.actual_load_x_positions):
                continue

            start_x = self.actual_load_x_positions[start_idx]
            end_x = self.actual_load_x_positions[end_idx]

            if start_x <= x_pos <= end_x:
                # 确认删除
                result = messagebox.askyesno("确认删除", f"确定要删除区间{i+1}吗？")
                if result:
                    # 删除区间
                    del self.actual_load_intervals[i]

                    # 保存到程序数据
                    if self.current_program_id and self.current_tool_key:
                        if self.current_program_id in self.programs_data:
                            if self.current_tool_key in self.programs_data[self.current_program_id]:
                                self.programs_data[self.current_program_id][self.current_tool_key]['intervals'] = self.actual_load_intervals.copy()
                            else:
                                # 兼容旧版本：如果没有tool_key，保存到程序级别
                                self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()
                    elif self.current_program_id and self.current_program_id in self.programs_data:
                        # 兼容旧版本：如果没有tool_key，保存到程序级别
                        self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()

                    # 重新绘制整个图表（包括区间高亮）
                    data_type = "滤波" if self.is_filtered else "原始"
                    self.plot_steady_intervals(data_type)
                    
                    # 重新绘制边界线
                    self.draw_interval_boundaries()

                    # 刷新区间详情与基准值，并保存状态
                    self.refresh_interval_ui(data_type)
                    
                    # 刷新刀具选择器（保持当前选择）
                    if hasattr(self, 'current_program_id') and self.current_program_id:
                        self.update_tool_selector(self.current_program_id, preserve_selection=True)

                    self.status_var_actual_load.set(f"已删除区间{i+1}")
                return

    def merge_all_overlapping_intervals(self):
        """通用的区间合并函数：合并所有重叠或包含的区间，返回处理的区间数"""
        if not self.actual_load_intervals or len(self.actual_load_intervals) < 2:
            return 0
        
        # 先按起始位置排序
        self.actual_load_intervals.sort(key=lambda x: x[0])
        
        total_processed = 0
        merged = []
        
        # 使用第一个区间作为当前合并区间
        current_start, current_end = self.actual_load_intervals[0]
        
        for i in range(1, len(self.actual_load_intervals)):
            next_start, next_end = self.actual_load_intervals[i]
            
            # 检查是否重叠或相邻（包含、重叠、紧邻的情况都合并）
            if next_start <= current_end:
                # 重叠或包含，扩展当前区间
                current_end = max(current_end, next_end)
                total_processed += 1
            else:
                # 不重叠，保存当前区间，开始新区间
                merged.append((current_start, current_end))
                current_start, current_end = next_start, next_end
        
        # 添加最后一个区间
        merged.append((current_start, current_end))
        
        # 更新区间列表
        self.actual_load_intervals = merged
        
        return total_processed
    
    def remove_contained_intervals(self):
        """移除被完全包含的区间，只保留最大的区间，返回被移除的区间数"""
        # 这个函数已被 merge_all_overlapping_intervals 取代，但保留以兼容
        return 0
    
    def auto_merge_overlapping_intervals(self):
        """自动合并重叠或相邻的区间，返回合并的组数"""
        # 使用通用的合并函数
        return self.merge_all_overlapping_intervals()

    def merge_selected_intervals(self):
        """合并选中的区间"""
        if len(self.selected_intervals) < 2:
            messagebox.showinfo("提示", "请至少选择2个区间进行合并")
            return

        # 排序选中的区间索引
        selected_sorted = sorted(self.selected_intervals)

        # 检查是否为连续的区间
        is_continuous = True
        for i in range(len(selected_sorted) - 1):
            if selected_sorted[i + 1] - selected_sorted[i] != 1:
                is_continuous = False
                break

        if not is_continuous:
            # 找出中间的区间
            middle_intervals = []
            for i in range(selected_sorted[0] + 1, selected_sorted[-1]):
                if i not in selected_sorted:
                    middle_intervals.append(i)
            
            if middle_intervals:
                result = messagebox.askyesno(
                    "警告",
                    f"选中的区间不连续，中间有 {len(middle_intervals)} 个区间将被一起合并。\n"
                    f"将合并区间 {selected_sorted[0]+1} 到区间 {selected_sorted[-1]+1}（包括中间所有区间）\n\n是否继续？",
                )
                if not result:
                    return
            # 将中间的区间也加入到合并列表
            for idx in middle_intervals:
                if idx not in selected_sorted:
                    selected_sorted.append(idx)
            selected_sorted.sort()

        # 获取合并后的起始和结束索引
        merge_start_idx = self.actual_load_intervals[selected_sorted[0]][0]
        merge_end_idx = self.actual_load_intervals[selected_sorted[-1]][1]

        # 删除原有的区间（从后往前删，避免索引问题）
        for i in reversed(selected_sorted):
            del self.actual_load_intervals[i]

        # 插入合并后的区间
        insert_pos = selected_sorted[0]
        self.actual_load_intervals.insert(insert_pos, (merge_start_idx, merge_end_idx))
        
        # 合并所有重叠区间
        additional_merged = self.merge_all_overlapping_intervals()

        # 保存到程序数据
        if self.current_program_id and self.current_tool_key:
            if self.current_program_id in self.programs_data:
                if self.current_tool_key in self.programs_data[self.current_program_id]:
                    self.programs_data[self.current_program_id][self.current_tool_key]['intervals'] = self.actual_load_intervals.copy()
                else:
                    # 兼容旧版本：如果没有tool_key，保存到程序级别
                    self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()
        elif self.current_program_id and self.current_program_id in self.programs_data:
            # 兼容旧版本：如果没有tool_key，保存到程序级别
            self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()

        # 清空选择
        self.selected_intervals = []

        # 重新绘制整个图表（包括区间高亮）
        data_type = "滤波" if self.is_filtered else "原始"
        self.plot_steady_intervals(data_type)

        # 刷新区间详情与平均值，并保存状态
        self.refresh_interval_ui(data_type)
        
        # 重新绘制边界线
        self.draw_interval_boundaries()

        total_merged = len(selected_sorted) - 1 + additional_merged
        self.status_var_actual_load.set(f"已合并区间，共处理 {total_merged} 组重叠")
    
    def add_new_interval(self):
        """交互式添加新区间 - 在图上选择起点和终点"""
        if not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        # 检查是否已经在添加模式中
        if hasattr(self, 'adding_interval_mode') and self.adding_interval_mode:
            messagebox.showinfo("提示", "已在添加区间模式中")
            return
        
        # 进入添加区间模式
        self.adding_interval_mode = True
        self.add_interval_points = []  # 存储选择的点 [start_x, end_x]
        self.add_interval_temp_line = None  # 临时显示的选择线
        
        # 修改按钮显示
        self.add_interval_button.config(text="✓ 选择中")
        
        # 连接鼠标点击事件
        self.add_interval_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_add_interval_click)
        
        # 显示提示信息
        self.status_var_actual_load.set("添加区间模式：请在图上点击选择起始位置，再点击结束位置（右键取消）")
    
    def on_add_interval_click(self, event):
        """处理添加区间时的鼠标点击"""
        if event.inaxes != self.ax_actual_load:
            return
        
        # 右键取消
        if event.button == 3:
            self.cancel_add_interval()
            return
        
        # 左键选择点
        if event.button == 1:
            x_click = event.xdata
            if x_click is None:
                return
            
            # 找到最接近的数据点索引
            closest_idx = self.find_closest_data_index(x_click)
            
            if len(self.add_interval_points) == 0:
                # 选择起始点
                self.add_interval_points.append(closest_idx)
                
                # 绘制起始点标记
                start_x = self.actual_load_x_positions[closest_idx]
                if self.add_interval_temp_line:
                    self.add_interval_temp_line.remove()
                self.add_interval_temp_line = self.ax_actual_load.axvline(
                    x=start_x, color='orange', linewidth=2, linestyle='--', alpha=0.7
                )
                self.canvas_actual_load.draw()
                
                self.status_var_actual_load.set(f"已选择起始位置 (索引: {closest_idx})，请点击选择结束位置（右键取消）")
                
            elif len(self.add_interval_points) == 1:
                # 选择结束点
                start_idx = self.add_interval_points[0]
                end_idx = closest_idx
                
                # 确保起始点小于结束点
                if end_idx <= start_idx:
                    messagebox.showwarning("无效选择", "结束位置必须在起始位置之后，请重新选择")
                    return
                
                # 检查是否与现有区间重叠
                overlap = False
                overlap_idx = -1
                for i, (existing_start, existing_end) in enumerate(self.actual_load_intervals):
                    if not (end_idx < existing_start or start_idx > existing_end):
                        overlap = True
                        overlap_idx = i + 1
                        break
                
                if overlap:
                    result = messagebox.askyesno(
                        "区间重叠",
                        f"选择的区间与第 {overlap_idx} 个现有区间重叠。\n是否仍要添加？"
                    )
                    if not result:
                        self.cancel_add_interval()
                        return
                
                # 添加新区间
                new_interval = (start_idx, end_idx)
                self.actual_load_intervals.append(new_interval)
                
                # 按起始位置排序
                self.actual_load_intervals.sort(key=lambda x: x[0])
                
                # 合并所有重叠区间
                merged = self.merge_all_overlapping_intervals()
                
                # 保存到程序数据
                if self.current_program_id and self.current_tool_key:
                    if self.current_program_id in self.programs_data:
                        if self.current_tool_key in self.programs_data[self.current_program_id]:
                            self.programs_data[self.current_program_id][self.current_tool_key]['intervals'] = self.actual_load_intervals.copy()
                        else:
                            # 兼容旧版本：如果没有tool_key，保存到程序级别
                            self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()
                elif self.current_program_id and self.current_program_id in self.programs_data:
                    # 兼容旧版本：如果没有tool_key，保存到程序级别
                    self.programs_data[self.current_program_id]['intervals'] = self.actual_load_intervals.copy()

                # 刷新区间详情与平均值，并保存状态
                data_type = "滤波" if self.is_filtered else "原始"
                self.refresh_interval_ui(data_type)

                # 退出添加模式
                self.finish_add_interval()
                
                # 重新绘制图表
                data_type = "滤波" if self.is_filtered else "原始"
                self.plot_steady_intervals(data_type)
                
                # 更新文本显示
                self.update_interval_display(data_type, self.reduce_interval_actual_load.get())
                
                # 如果处于微调模式，重新绘制边界线
                if hasattr(self, 'adjustment_mode') and self.adjustment_mode:
                    self.draw_interval_boundaries()
                
                # 保存状态并刷新刀具选择器（保持当前选择）
                self.save_current_program_state()
                if hasattr(self, 'current_program_id') and self.current_program_id:
                    self.update_tool_selector(self.current_program_id, preserve_selection=True)
                
                if merged > 0:
                    self.status_var_actual_load.set(f"✓ 已添加新区间，自动合并了 {merged} 个重叠区间")
                else:
                    self.status_var_actual_load.set(f"✓ 已添加新区间: [{start_idx}, {end_idx}]")
    
    def find_closest_data_index(self, x_value):
        """找到最接近给定x值的数据点索引"""
        x_positions = np.array(self.actual_load_x_positions)
        distances = np.abs(x_positions - x_value)
        closest_idx = np.argmin(distances)
        return int(closest_idx)
    
    def cancel_add_interval(self):
        """取消添加区间"""
        self.finish_add_interval()
        self.status_var_actual_load.set("已取消添加区间")
        
        # 清除临时标记
        if self.add_interval_temp_line:
            self.add_interval_temp_line.remove()
            self.add_interval_temp_line = None
            self.canvas_actual_load.draw()
    
    def finish_add_interval(self):
        """完成添加区间（清理状态）"""
        self.adding_interval_mode = False
        self.add_interval_points = []
        
        # 恢复按钮显示
        self.add_interval_button.config(text="➕ 添加")
        
        # 断开事件连接
        if hasattr(self, 'add_interval_cid') and self.add_interval_cid:
            self.canvas_actual_load.mpl_disconnect(self.add_interval_cid)
            self.add_interval_cid = None
        
        # 清除临时标记
        if hasattr(self, 'add_interval_temp_line') and self.add_interval_temp_line:
            try:
                self.add_interval_temp_line.remove()
            except:
                pass
            self.add_interval_temp_line = None
    
    def on_closing(self):
        """窗口关闭时的清理处理"""
        try:
            # 停止所有after回调
            if hasattr(self, 'root'):
                for after_id in self.root.tk.call('after', 'info').split():
                    try:
                        self.root.after_cancel(after_id)
                    except:
                        pass
            
            # 关闭所有matplotlib图形
            plt.close('all')
            
            # 清理图表相关资源
            if hasattr(self, 'canvas_actual_load'):
                try:
                    self.canvas_actual_load.get_tk_widget().destroy()
                except:
                    pass
            
            if hasattr(self, 'fig_actual_load'):
                try:
                    plt.close(self.fig_actual_load)
                except:
                    pass
            
            # 清理数据
            self.actual_load_data = None
            self.filtered_data = None
            self.segments = []
            
            # 强制垃圾回收
            gc.collect()
            
            # 销毁主窗口
            if hasattr(self, 'root'):
                self.root.quit()
                self.root.destroy()
            
        except Exception as e:
            print(f"关闭时发生错误: {e}")
        finally:
            # 确保进程完全退出
            import sys
            import os
            try:
                # 强制终止所有线程并退出
                os._exit(0)
            except:
                sys.exit(0)

    def adjust_figure_size(self):
        """调整图表大小以适应窗口"""
        try:
            if hasattr(self, 'actual_load_figure_frame'):
                frame_width = self.actual_load_figure_frame.winfo_width()
                frame_height = self.actual_load_figure_frame.winfo_height()
                
                if frame_width > 100 and frame_height > 100:
                    dpi = self.fig_actual_load.dpi
                    self.fig_actual_load.set_size_inches(frame_width / dpi, frame_height / dpi)
                    self.canvas_actual_load.draw_idle()
        except Exception:
            pass

    def show_actual_load_initial_message(self):
        """显示初始提示信息 - 科技感欢迎界面"""
        message = """╔═══════════════════════════════════════════════════╗
║    🚀 AFC 2.0 稳态区间分析系统                    ║
║                 v2.0 - 智能版                      ║
╚═══════════════════════════════════════════════════╝

📋 快速上手指南：
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1️⃣  选择程序和刀具
   → 从上方下拉菜单选择要分析的程序和刀具

2️⃣  自动区间划分
   → 点击 🚀 自动划分 进行智能分析
   → 调节灵敏度可获得不同的划分结果

3️⃣  结果微调（可选）
   → 点击 ✏️ 微调 进入精细调整模式
   → 拖动边界线、添加/删除/合并区间

4️⃣  保存结果
   → 点击 💾 保存 导出分析报告

💡 实用技巧：
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
• 🖱️  鼠标滚轮：图表横向缩放
• 🎛️  滤波功能：降低噪声，提升分析精度  
• 🔄  刷新：清除所有结果，重新开始

系统状态：✓ 就绪
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""
        self.actual_load_result_text.insert(tk.END, message)

def main(csv_file=None, txt_file=None):
    """
    主函数
    参数:
        csv_file: CSV数据文件路径（第1列=数据值，第2列=程序行号，第3列=程序号）
        txt_file: TXT映射文件路径（格式: 程序名:程序号;程序名:程序号;...）
    """
    root = tk.Tk()
    
    # 调试信息：显示传入的文件路径
    if csv_file and txt_file:
        root.title(f"实际负载稳态区间划分工具 - 已加载数据")
    else:
        root.title("实际负载稳态区间划分工具 - 未加载数据")
    
    app = ActualLoadAnalysis(root, csv_file, txt_file)
    root.mainloop()

if __name__ == "__main__":
    import sys
    import os

def get_executable_dir():
    """获取可执行文件所在目录（支持打包后的exe和开发环境）"""
    if getattr(sys, 'frozen', False):
        # 打包后的exe环境
        return os.path.dirname(sys.executable)
    else:
        # 开发环境
        return os.path.dirname(os.path.abspath(__file__))

def auto_find_data_files():
    """自动查找CSV和TXT文件"""
    exe_dir = get_executable_dir()
    
    # 查找策略1: 在exe同目录下查找 SampleData.csv 和 SampleData.txt
    csv_file = os.path.join(exe_dir, 'SampleData.csv')
    txt_file = os.path.join(exe_dir, 'SampleData.txt')
    
    if os.path.exists(csv_file) and os.path.exists(txt_file):
        return csv_file, txt_file
    
    # 查找策略2: 在exe同目录下的SampleData子目录中查找
    csv_file = os.path.join(exe_dir, 'SampleData', 'SampleData.csv')
    txt_file = os.path.join(exe_dir, 'SampleData', 'SampleData.txt')
    
    if os.path.exists(csv_file) and os.path.exists(txt_file):
        return csv_file, txt_file
    
    # 查找策略3: 查找任意的.csv和.txt文件
    csv_files = [f for f in os.listdir(exe_dir) if f.lower().endswith('.csv')]
    txt_files = [f for f in os.listdir(exe_dir) if f.lower().endswith('.txt')]
    
    if csv_files and txt_files:
        # 优先选择包含"sample"或"data"的文件
        csv_file = None
        txt_file = None
        
        for cf in csv_files:
            if 'sample' in cf.lower() or 'data' in cf.lower():
                csv_file = os.path.join(exe_dir, cf)
                break
        if not csv_file and csv_files:
            csv_file = os.path.join(exe_dir, csv_files[0])
        
        for tf in txt_files:
            if 'sample' in tf.lower() or 'data' in tf.lower():
                txt_file = os.path.join(exe_dir, tf)
                break
        if not txt_file and txt_files:
            txt_file = os.path.join(exe_dir, txt_files[0])
        
        if csv_file and txt_file:
            return csv_file, txt_file
    
    return None, None

# 检查命令行参数
if len(sys.argv) >= 3:
    # 从命令行接收文件路径
    csv_file = sys.argv[1]
    txt_file = sys.argv[2]
    main(csv_file, txt_file)
else:
    # 自动查找数据文件
    csv_file, txt_file = auto_find_data_files()
    
    if csv_file and txt_file:
        # 找到文件，自动加载
        main(csv_file, txt_file)
    else:
        # 无参数模式，启动空白界面
        main()

