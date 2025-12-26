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
# 在文件开头添加
import sys
import os
import gc
from scipy.signal import butter, filtfilt
import chardet
from sklearn.linear_model import LinearRegression
from sklearn.model_selection import train_test_split
from sklearn.metrics import mean_squared_error, r2_score


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

class MillingAnalysisTool:
    def __init__(self, root):
        self.root = root
        self.root.title("🔬 铣削工艺信息分析工具 - 智能分析系统")
        
        # 配置科技感主题样式
        self.setup_tech_theme()
        
        # 获取屏幕尺寸并设置自适应窗口大小
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        
        # 计算合适的窗口大小（屏幕的85%，但不超过最大尺寸，不小于最小尺寸）
        max_width, max_height = 1600, 1000
        min_width, min_height = 1000, 700
        
        window_width = min(max_width, max(min_width, int(screen_width * 0.85)))
        window_height = min(max_height, max(min_height, int(screen_height * 0.85)))
        
        # 计算居中位置
        center_x = (screen_width - window_width) // 2
        center_y = (screen_height - window_height) // 2
        
        # 设置窗口大小和位置
        self.root.geometry(f"{window_width}x{window_height}+{center_x}+{center_y}")
        
        # 设置最小窗口大小
        self.root.minsize(min_width, min_height)
        
        # 使窗口可调整大小
        self.root.resizable(True, True)
        
        # 初始化所有变量
        self.input_file_path = tk.StringVar()
        self.s_base = tk.DoubleVar(value=5000.0)  # 基准转速 (rpm)
        # 学术实验：去掉扭矩/电流系数，采用空间加工阻抗系数 Z(s) 进行功率映射
        self.p_idle = tk.DoubleVar(value=0.0)     # 空载功率 P_idle (W)
        self.p_rated = tk.DoubleVar(value=0.0)    # 额定功率 P_rated (W), 0 表示不启用硬约束
        self.z_impedance = tk.DoubleVar(value=120.0)  # 阻抗系数 Z(s) (W/(mm³/s))
        self.data = []  # 存储处理后的数据
        self.figures = []  # 存储图表对象
        self.current_figure_index = 0  # 当前显示的图表索引
        self.figure_names = []  # 图表名称列表
        self.min_length = tk.IntVar(value=100)  # 最小区间长度
        self.batch_min_length = 5  # 添加批量处理专用的点数变量
        self.encoding_var = tk.StringVar(value="auto")  # 文件编码
        self.currents = None  # 电流数据
        self.cumulative_time = None  # 累计时间
        self.intervals = None  # 稳态区间
        self.processed_file_path = ""  # 处理后的文件路径
        self.processed_data_dir = None  # 添加这个实例变量
        self.batch_files = []  # 存储批量处理的文件列表
        self.rapid_speed_xy = tk.DoubleVar(value=4800.0)  # XY平面快速移动速度
        self.rapid_speed_z = tk.DoubleVar(value=3600.0)    # Z方向快速移动速度
        self.batch_rapid_speed_xy = tk.DoubleVar(value=4800.0)  # 批量处理XY平面快速移动速度
        self.batch_rapid_speed_z = tk.DoubleVar(value=3600.0)    # 批量处理Z方向快速移动速度
        
        # 添加防抖动定时器，避免频繁调用resize
        self._resize_timer = None
        
        # 添加新变量（必须在创建标签页之前定义）
        self.tool_diameter = tk.DoubleVar(value=10.0)  # 刀具直径 (mm)
        self.workpiece_material = tk.StringVar(value="硬质合金铝用铣刀")  # 刀具材料
        self.blank_material = tk.StringVar(value="AL6061")  # 毛坯材料
        self.batch_tool_diameter = tk.DoubleVar(value=10.0)  # 批量处理刀具直径
        self.batch_workpiece_material = tk.StringVar(value="硬质合金铝用铣刀")  # 批量处理刀具材料
        self.batch_blank_material = tk.StringVar(value="AL6061")  # 批量处理毛坯材料
        
        # 添加波动阈值变量
        self.threshold = tk.DoubleVar(value=0.2)  # 波动阈值 (20%)
        self.steady_threshold = tk.DoubleVar(value=0.2)  # 稳态区间划分的波动阈值
        self.actual_current_threshold = tk.DoubleVar(value=0.2)  # 实际电流稳态区间划分的波动阈值
        self.batch_threshold = tk.DoubleVar(value=0.2)  # 批量处理的波动阈值
        
        # 添加滤波相关变量
        self.cutoff_freq = tk.DoubleVar(value=0.1)  # 截止频率
        self.filter_order = tk.IntVar(value=4)  # 滤波器阶数
        
        # 添加MRR稳态区间划分相关变量
        self.mrr_min_length = tk.DoubleVar(value=10.0)  # MRR稳态区间最小行程长度 (mm)
        self.enable_mrr_steady = tk.BooleanVar(value=True)  # 是否启用MRR稳态区间划分
        self.mrr_intervals = []  # 存储MRR稳态区间
        self.filtered_data = None  # 滤波后的数据
        self.is_filtered = False  # 滤波状态标志
        
        # 添加区间分割相关变量
        self.segment_points = []  # 存储分割点
        self.segment_lines = []  # 存储分割线对象
        self.segment_texts = []  # 存储分割点文字对象
        self.segments = []  # 存储分段数据和参数
        self.click_cid = None  # 点击事件连接ID
        
        # 添加分段参数管理
        self.current_segment_index = tk.IntVar(value=0)  # 当前选择的分段索引
        self.segment_params = {}  # 存储每个分段的参数 {segment_index: {参数字典}}
        self.segment_min_length = tk.IntVar(value=100)  # 当前分段的最小区间长度
        self.segment_threshold = tk.DoubleVar(value=0.2)  # 当前分段的波动阈值
        self.segment_abs_threshold = tk.DoubleVar(value=0.05)  # 当前分段的绝对波动阈值
        self.segment_reduce_interval = tk.BooleanVar(value=True)  # 当前分段的缩减区间边界
        
        # 图表交互功能变量
        self.original_xlim = None  # 原始x轴范围
        self.original_ylim = None  # 原始y轴范围
        self.scroll_cid = None  # 滚动事件连接ID
        self.zoom_factor = 1.2  # 缩放因子
        
        # 创建标签页
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 创建工艺信息分析标签页
        self.data_processing_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.data_processing_tab, text="工艺信息分析")
        # 学术实验：仅保留“工艺信息分析”标签页
        # 创建界面
        self.create_data_processing_tab()
        # self.create_steady_state_tab()  # 已合并到工艺信息分析页
        # 初始化图表
        self.init_figures()
        self.optimize_processing()  # 添加性能优化
        
        # 添加窗口大小变化监听器
        self.root.bind("<Configure>", self.on_window_resize)
        
        # 延迟调用图表大小自适应，确保所有组件都已创建完成
        self.root.after(100, self.adjust_figure_sizes)
        self.root.after(200, self.adjust_actual_load_chart_size)
    
    def create_actual_load_tab(self):
        """创建实际负载稳态区间划分标签页界面"""
        # 创建主容器
        main_container = ttk.Frame(self.actual_load_tab)
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # 创建画布和滚动条
        canvas = tk.Canvas(main_container, highlightthickness=0)
        v_scrollbar = ttk.Scrollbar(main_container, orient="vertical", command=canvas.yview)
        h_scrollbar = ttk.Scrollbar(main_container, orient="horizontal", command=canvas.xview)
        
        # 创建内容框架
        scrollable_frame = ttk.Frame(canvas)
        
        # 配置滚动
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # 布局滚动条和画布
        canvas.grid(row=0, column=0, sticky="nsew")
        v_scrollbar.grid(row=0, column=1, sticky="ns")
        h_scrollbar.grid(row=1, column=0, sticky="ew")
        
        # 配置网格权重
        main_container.grid_rowconfigure(0, weight=1)
        main_container.grid_columnconfigure(0, weight=1)
        
        # 自适应画布窗口大小
        def configure_scroll_region(event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            # 保持内容框架至少与画布一样宽
            canvas_width = canvas.winfo_width()
            req_width = scrollable_frame.winfo_reqwidth()
            if canvas_width > req_width:
                canvas.itemconfig(canvas_window, width=canvas_width)
        
        canvas.bind('<Configure>', configure_scroll_region)
        scrollable_frame.bind('<Configure>', configure_scroll_region)
        
        # 绑定鼠标滚轮事件（支持多平台）
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
        
        # 水平滚动（Shift+鼠标滚轮）
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
        
        # 主框架 - 保持原有的布局风格
        main_frame = ttk.Frame(scrollable_frame, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 输入文件选择
        input_frame = ttk.LabelFrame(main_frame, text="输入设置", padding="10")
        input_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(input_frame, text="输入文件:").grid(row=0, column=0, sticky=tk.W)
        self.actual_load_input_path = tk.StringVar()
        file_entry = ttk.Entry(input_frame, textvariable=self.actual_load_input_path)
        file_entry.grid(row=0, column=1, padx=5, sticky=tk.EW)  # 使用sticky=EW自适应宽度
        ttk.Button(input_frame, text="浏览...", command=self.browse_actual_load_file).grid(row=0, column=2)
        
        # 配置列权重，使文件输入框可以自适应扩展
        input_frame.columnconfigure(1, weight=1)
        
        # 添加编码选择
        ttk.Label(input_frame, text="文件编码:").grid(row=1, column=0, sticky=tk.W, pady=(10, 0))
        encoding_frame = ttk.Frame(input_frame)
        encoding_frame.grid(row=1, column=1, sticky=tk.W, pady=(10, 0))
        
        encodings = ["auto (自动检测)", "utf-8", "gbk", "gb2312", "latin1", "iso-8859-1", "cp1252"]
        self.actual_load_encoding_var = tk.StringVar(value="auto")
        ttk.Radiobutton(encoding_frame, text=encodings[0], variable=self.actual_load_encoding_var, value="auto").pack(side=tk.LEFT)
        ttk.Radiobutton(encoding_frame, text=encodings[1], variable=self.actual_load_encoding_var, value="utf-8").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[2], variable=self.actual_load_encoding_var, value="gbk").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[3], variable=self.actual_load_encoding_var, value="gb2312").pack(side=tk.LEFT, padx=5)
        
        # 横向排列的参数区域
        param_container = ttk.Frame(main_frame)
        param_container.pack(fill=tk.X, pady=5)
        
        # 数据源选择
        data_source_frame = ttk.LabelFrame(param_container, text="数据源选择", padding="10")
        data_source_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # 创建数据源选择变量
        self.data_source_var = tk.StringVar(value="current")
        
        # 创建按钮布局
        ttk.Radiobutton(data_source_frame, text="负载电流", variable=self.data_source_var, 
                    value="current", command=self.switch_data_source).pack(anchor=tk.W, pady=2)
        ttk.Radiobutton(data_source_frame, text="VGpro功率(G寄存器432)", variable=self.data_source_var, 
                    value="vgpro_power", command=self.switch_data_source).pack(anchor=tk.W, pady=2)
        ttk.Radiobutton(data_source_frame, text="华中模块功率(X寄存器108)", variable=self.data_source_var, 
                    value="huazhong_power", command=self.switch_data_source).pack(anchor=tk.W, pady=2)
        
        # 分析参数
        analysis_frame = ttk.LabelFrame(param_container, text="分析参数", padding="10")
        analysis_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        ttk.Label(analysis_frame, text="最小区间长度:").grid(row=0, column=0, sticky=tk.W)
        self.actual_load_min_length = tk.IntVar(value=100)
        ttk.Entry(analysis_frame, textvariable=self.actual_load_min_length, width=10).grid(row=0, column=1, padx=5, sticky=tk.W)
        
        ttk.Label(analysis_frame, text="(最小连续数据点数)").grid(row=0, column=2, padx=10, sticky=tk.W)
        
        # 添加波动阈值设置
        ttk.Label(analysis_frame, text="波动阈值:").grid(row=1, column=0, sticky=tk.W, pady=(10, 0))
        ttk.Entry(analysis_frame, textvariable=self.actual_current_threshold, width=10).grid(row=1, column=1, padx=5, sticky=tk.W)
        ttk.Label(analysis_frame, text="(例如: 0.2 表示20%波动)").grid(row=1, column=2, padx=10, sticky=tk.W)
        
        # 在参数设置区域添加绝对阈值输入
        ttk.Label(analysis_frame, text="绝对波动阈值:").grid(row=2, column=0, sticky=tk.W, pady=(10, 0))
        self.absolute_threshold = tk.DoubleVar(value=0.05)
        ttk.Entry(analysis_frame, textvariable=self.absolute_threshold, width=10).grid(row=2, column=1, padx=5, sticky=tk.W)
        ttk.Label(analysis_frame, text="(例如: 0.05 表示0.05绝对波动)").grid(row=2, column=2, padx=10, sticky=tk.W)
        
        # 添加是否缩减区间的复选框
        ttk.Label(analysis_frame, text="缩减区间边界:").grid(row=3, column=0, sticky=tk.W, pady=(10, 0))
        self.reduce_interval_actual_load = tk.BooleanVar(value=True)
        ttk.Checkbutton(analysis_frame, text="启用", variable=self.reduce_interval_actual_load).grid(row=3, column=1, sticky=tk.W)
        ttk.Label(analysis_frame, text="(禁用时将使用完整区间)").grid(row=3, column=2, padx=10, sticky=tk.W)
        
        # 滤波参数设置
        filter_frame = ttk.LabelFrame(param_container, text="滤波参数", padding="10")
        filter_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        ttk.Label(filter_frame, text="截止频率:").grid(row=0, column=0, sticky=tk.W)
        ttk.Entry(filter_frame, textvariable=self.cutoff_freq, width=10).grid(row=0, column=1, padx=5, sticky=tk.W)
        ttk.Label(filter_frame, text="(0.01-0.5, 值越小滤波越强)").grid(row=0, column=2, padx=10, sticky=tk.W)
        
        ttk.Label(filter_frame, text="滤波器阶数:").grid(row=1, column=0, sticky=tk.W, pady=(10, 0))
        ttk.Entry(filter_frame, textvariable=self.filter_order, width=10).grid(row=1, column=1, padx=5, sticky=tk.W)
        ttk.Label(filter_frame, text="(1-10, 值越大滤波效果越陡)").grid(row=1, column=2, padx=10, sticky=tk.W)
        
        # 区间分割参数设置
        segment_frame = ttk.LabelFrame(param_container, text="区间分割", padding="10")
        segment_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        ttk.Label(segment_frame, text="分割模式:").grid(row=0, column=0, sticky=tk.W)
        self.segment_mode = tk.BooleanVar(value=False)
        ttk.Checkbutton(segment_frame, text="启用", variable=self.segment_mode, command=self.toggle_segment_mode).grid(row=0, column=1, sticky=tk.W)
        ttk.Label(segment_frame, text="(在图上点击设置分割点)").grid(row=0, column=2, padx=10, sticky=tk.W)
        
        # 分割点操作按钮
        button_row1 = ttk.Frame(segment_frame)
        button_row1.grid(row=1, column=0, columnspan=3, pady=(10, 5), sticky=tk.W+tk.E)
        ttk.Button(button_row1, text="选择删除", command=self.selective_delete_segment_points).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(button_row1, text="清除全部", command=self.clear_segment_points).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(button_row1, text="创建分段", command=self.analyze_segments).pack(side=tk.LEFT, padx=5)
        
        # 图表交互按钮
        chart_control_frame = ttk.LabelFrame(segment_frame, text="图表交互", padding="5")
        chart_control_frame.grid(row=1, column=3, columnspan=2, padx=10, pady=(10, 5), sticky=tk.W+tk.E)
        ttk.Button(chart_control_frame, text="重置视图", command=self.reset_chart_view, width=10).pack(side=tk.LEFT, padx=2)
        
        # 使用说明标签
        ttk.Label(segment_frame, text="提示: 使用鼠标滚轮可缩放图表", font=('Arial', 8), foreground='gray').grid(row=3, column=0, columnspan=5, pady=5, sticky=tk.W)
        
        # 分段选择
        ttk.Label(segment_frame, text="选择分段:").grid(row=2, column=0, sticky=tk.W, pady=(10, 0))
        self.segment_combobox = ttk.Combobox(segment_frame, textvariable=self.current_segment_index, 
                                           values=[], state="readonly", width=10)
        self.segment_combobox.grid(row=2, column=1, padx=5, sticky=tk.W, pady=(10, 0))
        self.segment_combobox.bind("<<ComboboxSelected>>", self.on_segment_selected)
        
        # 分析选项
        analysis_options_frame = ttk.Frame(segment_frame)
        analysis_options_frame.grid(row=2, column=2, padx=10, sticky=tk.W, pady=(10, 0))
        
        ttk.Button(analysis_options_frame, text="单独分析", command=self.analyze_single_segment).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(analysis_options_frame, text="合并执行", command=self.analyze_all_segments_merged).pack(side=tk.LEFT)
        
        # 当前分段参数设置框架（移动到与其他参数框架同一排）
        current_segment_frame = ttk.LabelFrame(param_container, text="当前分段参数", padding="10")
        current_segment_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # 参数设置使用紧凑的网格布局
        ttk.Label(current_segment_frame, text="最小区间长度:").grid(row=0, column=0, sticky=tk.W)
        ttk.Entry(current_segment_frame, textvariable=self.segment_min_length, width=8).grid(row=0, column=1, padx=2, sticky=tk.W)
        
        ttk.Label(current_segment_frame, text="波动阈值:").grid(row=1, column=0, sticky=tk.W, pady=(5, 0))
        ttk.Entry(current_segment_frame, textvariable=self.segment_threshold, width=8).grid(row=1, column=1, padx=2, sticky=tk.W, pady=(5, 0))
        
        ttk.Label(current_segment_frame, text="绝对波动阈值:").grid(row=2, column=0, sticky=tk.W, pady=(5, 0))
        ttk.Entry(current_segment_frame, textvariable=self.segment_abs_threshold, width=8).grid(row=2, column=1, padx=2, sticky=tk.W, pady=(5, 0))
        
        ttk.Label(current_segment_frame, text="缩减区间边界:").grid(row=3, column=0, sticky=tk.W, pady=(5, 0))
        ttk.Checkbutton(current_segment_frame, text="启用", variable=self.segment_reduce_interval).grid(row=3, column=1, sticky=tk.W, pady=(5, 0))
        
        # 添加从整体参数复制的按钮
        copy_params_frame = ttk.Frame(current_segment_frame)
        copy_params_frame.grid(row=4, column=0, columnspan=2, pady=(10, 0), sticky=tk.W)
        ttk.Button(copy_params_frame, text="从整体参数复制", command=self.copy_global_params_to_segment).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Button(copy_params_frame, text="保存当前参数", command=self.save_current_segment_params_manual).pack(side=tk.LEFT)
        
        # 按钮区域
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(pady=10)
        
        load_btn = ttk.Button(button_frame, text="加载数据", command=self.load_actual_load_data)
        load_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        # 替换“应用滤波”为“生成包络”
        filter_btn = ttk.Button(button_frame, text="应用滤波", command=self.apply_filter)
        filter_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        analyze_btn = ttk.Button(button_frame, text="运行分析", command=self.analyze_actual_load_data)
        analyze_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        save_btn = ttk.Button(button_frame, text="保存结果", command=self.save_actual_load_results)
        save_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        # 状态栏
        self.status_var_actual_load = tk.StringVar()
        self.status_var_actual_load.set("就绪")
        status_bar = ttk.Label(self.actual_load_tab, textvariable=self.status_var_actual_load, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 图表区域
        self.actual_load_figure_frame = ttk.Frame(main_frame)
        self.actual_load_figure_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # 初始化图表（使用更大尺寸和更高DPI以获得更好的显示效果）
        self.fig_actual_load = plt.figure(figsize=(16, 9), dpi=120, tight_layout=False)
        
        # 设置白色背景
        self.fig_actual_load.patch.set_facecolor('white')  # 白色背景
        
        # 调整子图边距，让图表居中对称显示
        self.fig_actual_load.subplots_adjust(
            left=0.10,     # 左边距 - 为y轴标签留出空间
            bottom=0.08,   # 下边距 - 为x轴标签留出空间
            right=0.90,    # 右边距 - 对称设置
            top=0.94,      # 上边距 - 为标题留出空间
            wspace=0.12,   # 子图间水平间距
            hspace=0.12    # 子图间垂直间距
        )
        
        self.ax_actual_load = self.fig_actual_load.add_subplot(111)
        # 设置坐标系背景为白色
        self.ax_actual_load.set_facecolor('white')
        
        # 创建画布并确保完全填充父框架
        self.canvas_actual_load = FigureCanvasTkAgg(self.fig_actual_load, master=self.actual_load_figure_frame)
        canvas_widget = self.canvas_actual_load.get_tk_widget()
        canvas_widget.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)
        
        # 配置画布以自适应大小
        canvas_widget.configure(relief=tk.FLAT, bd=0)
        
        # 添加导航工具栏，固定在底部
        self.toolbar_actual_load = NavigationToolbar2Tk(self.canvas_actual_load, self.actual_load_figure_frame)
        self.toolbar_actual_load.update()
        self.toolbar_actual_load.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 分段结果管理界面
        self.create_segment_results_panel(main_frame)
        
        # 结果显示区域
        result_frame = ttk.LabelFrame(main_frame, text="稳态区间详情", padding="10")
        result_frame.pack(fill=tk.X, pady=5)
        
        # 创建文本区域显示结果
        self.actual_load_result_text = tk.Text(result_frame, height=6, wrap=tk.WORD)
        self.actual_load_result_text.pack(fill=tk.BOTH, expand=True)
        scrollbar = ttk.Scrollbar(result_frame, command=self.actual_load_result_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.actual_load_result_text.config(yscrollcommand=scrollbar.set)


        self.filtered_data = None
        self.is_filtered = False
        self.current_data_source = "current"
        # 初始化数据存储
        self.actual_load_data = []
        self.actual_load_line_numbers = []
        self.actual_load_point_indices = []
        self.actual_load_x_positions = []
        self.actual_load_unique_line_numbers = []
        self.actual_load_intervals = []
        self.actual_load_interval_values = []
        # 稳态分析的程序行号和点数索引
        self.steady_line_numbers = []
        self.steady_point_indices = []
        self.merge_range_var = tk.StringVar(value="")
        # 初始提示
        self.show_actual_load_initial_message()
        
        # 设置图表交互功能（鼠标滚轮缩放）
        self.setup_chart_interactions()

    def create_segment_results_panel(self, parent):
        """创建分段结果管理面板"""
        segment_results_frame = ttk.LabelFrame(parent, text="分段结果管理", padding="10")
        segment_results_frame.pack(fill=tk.X, pady=5)
        
        # 左侧控制区域
        control_frame = ttk.Frame(segment_results_frame)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # 分段选择和显示控制
        display_frame = ttk.LabelFrame(control_frame, text="显示控制", padding="5")
        display_frame.pack(fill=tk.X, pady=(0, 5))
        
        # 显示模式选择
        ttk.Label(display_frame, text="显示模式:").grid(row=0, column=0, sticky=tk.W, pady=2)
        self.display_mode_var = tk.StringVar(value="all")
        mode_frame = ttk.Frame(display_frame)
        mode_frame.grid(row=0, column=1, sticky=tk.W, padx=(5, 0))
        
        ttk.Radiobutton(mode_frame, text="全部", variable=self.display_mode_var, 
                       value="all", command=self.update_segment_display).pack(side=tk.LEFT, padx=2)
        ttk.Radiobutton(mode_frame, text="合并", variable=self.display_mode_var, 
                       value="merged", command=self.update_segment_display).pack(side=tk.LEFT, padx=2)
        ttk.Radiobutton(mode_frame, text="单独", variable=self.display_mode_var, 
                       value="single", command=self.update_segment_display).pack(side=tk.LEFT, padx=2)
        
        # 分段选择（用于单独显示模式）
        ttk.Label(display_frame, text="选择分段:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.display_segment_var = tk.StringVar()
        self.display_segment_combobox = ttk.Combobox(display_frame, textvariable=self.display_segment_var, 
                                                    width=12, state="readonly")
        self.display_segment_combobox.grid(row=1, column=1, sticky=tk.W, padx=(5, 0))
        self.display_segment_combobox.bind('<<ComboboxSelected>>', self.update_segment_display)
        
        # 操作按钮
        button_frame = ttk.Frame(control_frame)
        button_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(button_frame, text="刷新结果", command=self.refresh_segment_results).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="导出详情", command=self.export_segment_details).pack(side=tk.LEFT, padx=2)
        
        # 右侧结果表格区域
        table_frame = ttk.Frame(segment_results_frame)
        table_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # 创建树形表格显示分段结果
        columns = ('分段', '参数设置', '稳态区间数', '区间详情')
        self.segment_results_tree = ttk.Treeview(table_frame, columns=columns, show='headings', height=6)
        
        # 设置列标题和宽度
        self.segment_results_tree.heading('分段', text='分段')
        self.segment_results_tree.heading('参数设置', text='参数设置')
        self.segment_results_tree.heading('稳态区间数', text='稳态区间数')
        self.segment_results_tree.heading('区间详情', text='区间详情')
        
        self.segment_results_tree.column('分段', width=60, anchor=tk.CENTER)
        self.segment_results_tree.column('参数设置', width=150, anchor=tk.W)
        self.segment_results_tree.column('稳态区间数', width=80, anchor=tk.CENTER)
        self.segment_results_tree.column('区间详情', width=300, anchor=tk.W)
        
        # 添加滚动条
        tree_scrollbar = ttk.Scrollbar(table_frame, orient=tk.VERTICAL, command=self.segment_results_tree.yview)
        self.segment_results_tree.configure(yscrollcommand=tree_scrollbar.set)
        
        # 布局
        self.segment_results_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 绑定双击事件
        self.segment_results_tree.bind("<Double-1>", self.on_segment_result_double_click)

    def manual_merge_intervals(self):
        """手动合并指定的区间"""
        if not hasattr(self, 'current_intervals') or not self.current_intervals:
            messagebox.showwarning("无区间", "请先运行分析获取区间")
            return
        
        merge_range_str = self.merge_range_var.get().strip()
        if not merge_range_str:
            messagebox.showwarning("输入错误", "请输入要合并的区间范围，例如'1-3'")
            return
        
        # 解析输入，例如"1-3" -> [1,3]
        try:
            parts = merge_range_str.split('-')
            if len(parts) != 2:
                raise ValueError
            start_idx = int(parts[0]) - 1  # 从1开始编号，转成0基
            end_idx = int(parts[1]) - 1
            if start_idx < 0 or end_idx >= len(self.current_intervals) or start_idx > end_idx:
                messagebox.showerror("输入错误", f"区间编号应在1-{len(self.current_intervals)}之间，且起始编号不大于结束编号")
                return
        except ValueError:
            messagebox.showerror("输入错误", "请输入有效的区间范围，例如'1-3'")
            return
        
        # 合并区间
        intervals_to_merge = self.current_intervals[start_idx:end_idx+1]
        merged_start = intervals_to_merge[0][0]
        merged_end = intervals_to_merge[-1][1]
        
        # 创建新的区间列表
        new_intervals = self.current_intervals[:start_idx]
        new_intervals.append((merged_start, merged_end))
        new_intervals.extend(self.current_intervals[end_idx+1:])
        
        # 更新当前区间
        self.current_intervals = new_intervals
        self.actual_load_intervals = new_intervals
        
        # 更新显示和图表
        self.update_interval_display("手动合并后", self.reduce_interval_actual_load.get())
        self.plot_steady_intervals("手动合并后")
        
        self.status_var_actual_load.set(f"手动合并完成! 当前区间数: {len(self.current_intervals)}")

    def update_interval_display(self, data_type, reduce_interval):
        """更新区间显示"""
        self.actual_load_result_text.delete(1.0, tk.END)
        interval_count = len(self.actual_load_intervals) if self.actual_load_intervals else 0
        self.actual_load_result_text.insert(tk.END, f"使用{data_type}数据找到 {interval_count} 个稳态区间:\n\n")
        self.actual_load_result_text.insert(tk.END, "区间\t\t\t长度(点)\n")
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
        
        for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
            # 索引边界保护
            if (start_idx < 0 or end_idx < 0 or
                start_idx >= data_len or end_idx >= data_len or
                start_idx >= line_len or end_idx >= line_len or
                start_idx >= point_len or end_idx >= point_len or
                start_idx > end_idx):
                continue  # 跳过异常区间
            
            try:
                # 获取程序行号和行内索引
                start_ln = self.actual_load_line_numbers[start_idx]
                start_point_idx = self.actual_load_point_indices[start_idx]
                end_ln = self.actual_load_line_numbers[end_idx]
                end_point_idx = self.actual_load_point_indices[end_idx]
                
                length_points = end_idx - start_idx + 1
                
                # 使用新格式显示区间
                self.actual_load_result_text.insert(
                    tk.END,
                    f"[{start_ln:.0f}.{start_point_idx}, {end_ln:.0f}.{end_point_idx}]\t"
                    f"{length_points}\n"
                )
            except Exception:
                # 单个区间异常不影响其它区间
                continue
        
        if not self.actual_load_interval_values:
            self.actual_load_result_text.insert(tk.END, "\n未能生成有效区间，请检查阈值设置或重新加载数据。\n")

    def plot_steady_intervals(self, data_type):
        """绘制稳态区间"""
        self.ax_actual_load.clear()
        # 设置白色背景
        self.ax_actual_load.set_facecolor('white')
        
        # 空值防护
        if (self.actual_load_data is None or self.actual_load_x_positions is None or
                len(self.actual_load_data) == 0):
            self.ax_actual_load.text(0.5, 0.5, "无数据可绘制", ha='center', va='center', 
                                    color='#333333', fontsize=16, fontweight='bold')
            self.canvas_actual_load.draw()
            return
        
        # 绘制所有数据点
        self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data,
                                 '-', color='#1f77b4', linewidth=2.5, label=f'{self.get_data_source_name()}值', 
                                 alpha=0.9, zorder=5)
        
        # 如果有滤波数据，也绘制滤波后的数据
        if self.is_filtered and self.filtered_data is not None:
            self.ax_actual_load.plot(self.actual_load_x_positions, self.filtered_data,
                                     '-', color='#ff7f0e', linewidth=3.0, label='滤波后数据', 
                                     alpha=0.95, zorder=6)
        
        # 标记稳态区间 - 使用清晰的配色
        if self.actual_load_intervals:
            # 使用淡色背景区分区间
            interval_colors = [
                '#ffcccc',  # 淡红
                '#ccffcc',  # 淡绿
                '#ccccff',  # 淡蓝
                '#ffffcc',  # 淡黄
                '#ffccff',  # 淡紫
                '#ccffff',  # 淡青
                '#ffddcc',  # 淡橙
                '#ddffcc',  # 淡草绿
            ]
            for idx, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
                if start_idx < 0 or end_idx >= len(self.actual_load_x_positions):
                    continue
                start_x = self.actual_load_x_positions[start_idx]
                end_x = self.actual_load_x_positions[end_idx]
                color = interval_colors[idx % len(interval_colors)]
                self.ax_actual_load.axvspan(start_x, end_x, alpha=0.5, color=color, 
                                           edgecolor='black', linewidth=1.5, zorder=1)
                
                # 添加边界线
                self.ax_actual_load.axvline(x=start_x, color='red', linewidth=2.0, alpha=0.7, 
                                           linestyle='--', zorder=4)
                self.ax_actual_load.axvline(x=end_x, color='red', linewidth=2.0, alpha=0.7, 
                                           linestyle='--', zorder=4)
        
        # 重新绘制分割线（确保它们在所有操作后保持显示）
        self.redraw_segment_lines()
        
        # 显示绝对阈值线
        try:
            absolute_threshold = self.absolute_threshold.get()
            if absolute_threshold > 0:
                # 画一条红色虚线表示绝对阈值
                self.ax_actual_load.axhline(y=absolute_threshold, color='#d62728', linestyle='--', 
                                          linewidth=2.5, alpha=0.9, 
                                          label=f'绝对阈值 ({absolute_threshold})', zorder=3)
        except:
            pass  # 如果获取阈值失败，不影响其他绘制
        
        # 根据数据源设置标题和标签
        data_source = self.data_source_var.get()
        if data_source == "current":
            title = f'负载电流稳态区间 ({data_type}数据)'
            ylabel = '电流 (A)'
        elif data_source == "vgpro_power":
            title = f'VGpro功率稳态区间 ({data_type}数据)'
            ylabel = '功率'
        else:  # huazhong_power
            title = f'华中模块功率稳态区间 ({data_type}数据)'
            ylabel = '功率'
        
        # 设置标题和标签
        self.ax_actual_load.set_title(title, fontsize=18, fontweight='bold', pad=15, 
                                     color='#333333')
        self.ax_actual_load.set_xlabel('程序行号位置', fontsize=14, fontweight='bold', 
                                      color='#333333')
        self.ax_actual_load.set_ylabel(ylabel, fontsize=14, fontweight='bold', 
                                      color='#333333')
        
        # 设置横轴刻度标签
        unique_line_numbers = self.actual_load_unique_line_numbers
        if len(unique_line_numbers) == 1:
            n = unique_line_numbers[0]
            self.ax_actual_load.set_xticks([n, n+0.5, n+1])
            self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"], 
                                               fontsize=12, color='#333333')
        elif len(unique_line_numbers) > 20:
            step = max(1, len(unique_line_numbers) // 10)
            tick_positions = range(0, len(unique_line_numbers), step)
            tick_labels = [str(unique_line_numbers[i]) for i in tick_positions]
            self.ax_actual_load.set_xticks(tick_positions)
            self.ax_actual_load.set_xticklabels(tick_labels, rotation=45, ha='right', 
                                               fontsize=12, color='#333333')
        else:
            self.ax_actual_load.set_xticks(range(len(unique_line_numbers)))
            self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], 
                                               rotation=45, ha='right', fontsize=12, color='#333333')
        
        # 设置y轴刻度标签字体大小和颜色
        self.ax_actual_load.tick_params(axis='y', labelsize=12, colors='#333333')
        self.ax_actual_load.tick_params(axis='x', colors='#333333')
        
        # 重新绘制分割线（确保它们在所有操作后保持显示）
        self.redraw_segment_lines()
        
        # 限制纵向高度不超过数据最高的1.2倍
        self.cap_y_axis(self.ax_actual_load, [self.actual_load_data, self.filtered_data])
        
        # 设置网格样式
        self.ax_actual_load.grid(True, linestyle=':', alpha=0.3, linewidth=0.5, 
                                color='gray', zorder=0)
        
        # 设置坐标轴边框颜色
        for spine in self.ax_actual_load.spines.values():
            spine.set_edgecolor('#333333')
            spine.set_linewidth(1.5)
        
        # 优化图例位置和样式
        legend = self.ax_actual_load.legend(loc='upper right', fontsize=12, framealpha=0.9, 
                                           shadow=True, fancybox=True)
        legend.get_frame().set_facecolor('white')
        legend.get_frame().set_edgecolor('#333333')
        legend.get_frame().set_linewidth(1.5)
        for text in legend.get_texts():
            text.set_color('#333333')
        
        # 优化布局以居中对称
        self.fig_actual_load.subplots_adjust(
            left=0.10, bottom=0.08, right=0.90, top=0.94,
            wspace=0.12, hspace=0.12
        )
        
        self.canvas_actual_load.draw()

    def plot_single_segment_analysis(self, segment_index, intervals, data_type):
        """绘制单个分段的分析结果，高亮显示当前分析的分段"""
        self.ax_actual_load.clear()
        # 应用科技感主题
        self.apply_tech_theme_to_axes(self.ax_actual_load)
        
        # 空值防护
        if (self.actual_load_data is None or self.actual_load_x_positions is None or
                len(self.actual_load_data) == 0):
            self.ax_actual_load.text(0.5, 0.5, "无数据可绘制", ha='center', va='center',
                                    color='#00ff41', fontsize=16, fontweight='bold')
            self.canvas_actual_load.draw()
            return
        
        # 获取当前分段信息
        current_segment = None
        for seg in self.segments:
            if seg['index'] == segment_index + 1:
                current_segment = seg
                break
        
        if current_segment is None:
            # 如果找不到分段，使用普通绘制方法
            self.plot_steady_intervals(data_type)
            return
        
        # 绘制所有数据点 - 分段显示不同透明度
        for i, seg in enumerate(self.segments):
            start_idx = seg['start_idx']
            end_idx = seg['end_idx']
            
            if i == segment_index:
                # 当前分析的分段，使用高亮显示
                self.ax_actual_load.plot(
                    self.actual_load_x_positions[start_idx:end_idx], 
                    self.actual_load_data[start_idx:end_idx],
                    '-', color='#00d4ff', linewidth=3.0, alpha=1.0, 
                    label=f'分段{i+1}(当前分析)', zorder=5
                )
                
                # 如果有滤波数据，也高亮显示
                if self.is_filtered and self.filtered_data is not None:
                    self.ax_actual_load.plot(
                        self.actual_load_x_positions[start_idx:end_idx], 
                        self.filtered_data[start_idx:end_idx],
                        '-', color='#ff00ff', linewidth=3.0, alpha=1.0, 
                        label=f'分段{i+1}滤波后(当前分析)', zorder=6
                    )
            else:
                # 其他分段，使用较淡的显示
                self.ax_actual_load.plot(
                    self.actual_load_x_positions[start_idx:end_idx], 
                    self.actual_load_data[start_idx:end_idx],
                    '-', color='#556677', linewidth=1.2, alpha=0.4, zorder=2
                )
        
        # 标记当前分段的稳态区间 - 使用高对比度霓虹色
        if intervals:
            interval_colors = [
                '#00ff41', '#ff3366', '#ffff00', '#00ffff', 
                '#ff9500', '#9d00ff', '#00ff9d', '#ff006e',
            ]
            for idx, (start_idx, end_idx) in enumerate(intervals):
                if start_idx < 0 or end_idx >= len(self.actual_load_x_positions):
                    continue
                start_x = self.actual_load_x_positions[start_idx]
                end_x = self.actual_load_x_positions[end_idx]
                color = interval_colors[idx % len(interval_colors)]
                self.ax_actual_load.axvspan(start_x, end_x, alpha=0.18, color=color, 
                                          edgecolor=color, linewidth=2.0, zorder=1,
                                          label='稳态区间' if idx == 0 else "")
                
                # 添加更清晰明亮的纵向边界线
                self.ax_actual_load.axvline(x=start_x, color=color, linewidth=2.5, alpha=0.9, 
                                           linestyle='--', zorder=4)
                self.ax_actual_load.axvline(x=end_x, color=color, linewidth=2.5, alpha=0.9, 
                                           linestyle='--', zorder=4)
        
        # 高亮当前分析的分段范围
        seg_start_x = self.actual_load_x_positions[current_segment['start_idx']]
        seg_end_x = self.actual_load_x_positions[current_segment['end_idx']-1]
        self.ax_actual_load.axvspan(seg_start_x, seg_end_x, alpha=0.15, color='#ffff00', 
                                  edgecolor='#ff9500', linewidth=2.0, zorder=0,
                                  label=f'分段{segment_index+1}范围')
        
        # 重新绘制分割线
        self.redraw_segment_lines()
        
        # 设置标题和标签
        data_source = self.data_source_var.get()
        if data_source == "current":
            title = f'分段{segment_index+1}负载电流稳态区间分析'
            ylabel = '电流 (A)'
        elif data_source == "vgpro_power":
            title = f'分段{segment_index+1}VGpro功率稳态区间分析'
            ylabel = '功率'
        else:
            title = f'分段{segment_index+1}华中模块功率稳态区间分析'
            ylabel = '功率'
        
        self.ax_actual_load.set_title(title, fontsize=20, fontweight='bold', pad=20, color='#00ff41')
        self.ax_actual_load.set_xlabel('程序行号位置', fontsize=15, fontweight='bold', color='#00d4ff')
        self.ax_actual_load.set_ylabel(ylabel, fontsize=15, fontweight='bold', color='#00d4ff')
        
        # 设置横轴刻度标签
        unique_line_numbers = self.actual_load_unique_line_numbers
        if len(unique_line_numbers) == 1:
            n = unique_line_numbers[0]
            self.ax_actual_load.set_xticks([n, n+0.5, n+1])
            self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"], fontsize=9)
        elif len(unique_line_numbers) > 20:
            step = max(1, len(unique_line_numbers) // 10)
            tick_positions = range(0, len(unique_line_numbers), step)
        # 设置横轴刻度标签 - 应用科技感样式（注意这是在单个分段分析函数中）
        unique_line_numbers = self.actual_load_unique_line_numbers
        if len(unique_line_numbers) == 1:
            n = unique_line_numbers[0]
            self.ax_actual_load.set_xticks([n, n+0.5, n+1])
            self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"], 
                                               fontsize=13, color='#aabbcc')
        elif len(unique_line_numbers) > 20:
            step = max(1, len(unique_line_numbers) // 10)
            tick_positions = range(0, len(unique_line_numbers), step)
            tick_labels = [str(unique_line_numbers[i]) for i in tick_positions]
            self.ax_actual_load.set_xticks(tick_positions)
            self.ax_actual_load.set_xticklabels(tick_labels, rotation=45, ha='right', 
                                               fontsize=13, color='#aabbcc')
        else:
            self.ax_actual_load.set_xticks(range(len(unique_line_numbers)))
            self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], 
                                               rotation=45, ha='right', fontsize=13, color='#aabbcc')
        
        # 限制纵向高度不超过数据最高的1.2倍
        self.cap_y_axis(self.ax_actual_load, [self.actual_load_data, self.filtered_data])
        
        # 去重图例并应用科技感样式
        handles, labels = self.ax_actual_load.get_legend_handles_labels()
        by_label = dict(zip(labels, handles))
        legend = self.ax_actual_load.legend(by_label.values(), by_label.keys(), 
                                           loc='upper right', fontsize=13, framealpha=0.85, 
                                           shadow=True, fancybox=True)
        legend.get_frame().set_facecolor('#0a0e27')
        legend.get_frame().set_edgecolor('#00d4ff')
        legend.get_frame().set_linewidth(2)
        for text in legend.get_texts():
            text.set_color('#ffffff')
        
        # 优化布局以充分利用图表区域
        self.fig_actual_load.subplots_adjust(
            left=0.07, bottom=0.08, right=0.98, top=0.95,
            wspace=0.12, hspace=0.12
        )
        
        self.canvas_actual_load.draw()

    def plot_merged_segments_analysis(self, data_type):
        """绘制所有分段的合并分析结果，只显示稳态区间边界线"""
        self.ax_actual_load.clear()
        # 应用科技感主题
        self.apply_tech_theme_to_axes(self.ax_actual_load)
        
        # 空值防护
        if (self.actual_load_data is None or self.actual_load_x_positions is None or
                len(self.actual_load_data) == 0):
            self.ax_actual_load.text(0.5, 0.5, "无数据可绘制", ha='center', va='center',
                                    color='#00ff41', fontsize=16, fontweight='bold')
            self.canvas_actual_load.draw()
            return
        
        # 绘制全部数据点 - 使用科技感霓虹配色
        self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data,
                                 '-', color='#00d4ff', linewidth=2.5, alpha=0.9, 
                                 label=f'{self.get_data_source_name()}值', zorder=5)
        
        # 如果有滤波数据，也绘制滤波后的数据
        if self.is_filtered and self.filtered_data is not None:
            self.ax_actual_load.plot(self.actual_load_x_positions, self.filtered_data,
                                     '-', color='#ff00ff', linewidth=3.0, alpha=0.95, 
                                     label='滤波后数据', zorder=6)
        
        # 绘制所有分段的稳态区间高亮背景和边界线
        legend_added = set()  # 避免重复的图例
        
        # 使用高对比度霓虹配色
        interval_colors = [
            '#00ff41', '#ff3366', '#ffff00', '#00ffff', 
            '#ff9500', '#9d00ff', '#00ff9d', '#ff006e',
        ]
        interval_idx = 0
        for i, segment in enumerate(self.segments):
            # 绘制该分段的稳态区间
            if 'intervals' in segment and segment['intervals']:
                for start_interval, end_interval in segment['intervals']:
                    if start_interval < 0 or end_interval >= len(self.actual_load_x_positions):
                        continue
                    start_x = self.actual_load_x_positions[start_interval]
                    end_x = self.actual_load_x_positions[end_interval]
                    
                    color = interval_colors[interval_idx % len(interval_colors)]
                    interval_idx += 1
                    # 绘制稳态区间的背景高亮
                    self.ax_actual_load.axvspan(start_x, end_x, alpha=0.18, color=color,
                                              edgecolor=color, linewidth=2.0, zorder=1,
                                              label='稳态区间' if '稳态区间' not in legend_added else "")
                    legend_added.add('稳态区间')
                    
                    # 绘制纵向边界线 - 使用霓虹虚线样式
                    # 起始边界线
                    self.ax_actual_load.axvline(x=start_x, color=color, linestyle='--', 
                                              linewidth=2.5, alpha=0.9, zorder=4,
                                              label='稳态区间边界' if '稳态区间边界' not in legend_added else "")
                    
                    # 结束边界线
                    self.ax_actual_load.axvline(x=end_x, color=color, linestyle='--', 
                                              linewidth=2.5, alpha=0.9, zorder=4)
                    legend_added.add('稳态区间边界')
        
        # 重新绘制分割线
        self.redraw_segment_lines()
        
        # 设置标题和标签 - 科技感样式
        data_source = self.data_source_var.get()
        if data_source == "current":
            title = f'所有分段负载电流稳态区间合并分析'
            ylabel = '电流 (A)'
        elif data_source == "vgpro_power":
            title = f'所有分段VGpro功率稳态区间合并分析'
            ylabel = '功率'
        else:
            title = f'所有分段华中模块功率稳态区间合并分析'
            ylabel = '功率'
        
        self.ax_actual_load.set_title(title, fontsize=20, fontweight='bold', pad=20, color='#00ff41')
        self.ax_actual_load.set_xlabel('程序行号位置', fontsize=15, fontweight='bold', color='#00d4ff')
        self.ax_actual_load.set_ylabel(ylabel, fontsize=15, fontweight='bold', color='#00d4ff')
        
        # 设置横轴刻度标签 - 科技感样式
        unique_line_numbers = self.actual_load_unique_line_numbers
        if len(unique_line_numbers) == 1:
            n = unique_line_numbers[0]
            self.ax_actual_load.set_xticks([n, n+0.5, n+1])
            self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"], 
                                               fontsize=13, color='#aabbcc')
        elif len(unique_line_numbers) > 20:
            step = max(1, len(unique_line_numbers) // 10)
            tick_positions = range(0, len(unique_line_numbers), step)
            tick_labels = [str(unique_line_numbers[i]) for i in tick_positions]
            self.ax_actual_load.set_xticks(tick_positions)
            self.ax_actual_load.set_xticklabels(tick_labels, rotation=45, ha='right', 
                                               fontsize=13, color='#aabbcc')
        else:
            self.ax_actual_load.set_xticks(range(len(unique_line_numbers)))
            self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], 
                                               rotation=45, ha='right', fontsize=13, color='#aabbcc')
        
        # 限制纵向高度不超过数据最高的1.2倍
        self.cap_y_axis(self.ax_actual_load, [self.actual_load_data, self.filtered_data])
        
        # 整理图例，避免重复 - 科技感样式
        handles, labels = self.ax_actual_load.get_legend_handles_labels()
        by_label = dict(zip(labels, handles))
        legend = self.ax_actual_load.legend(by_label.values(), by_label.keys(), 
                                           loc='upper right', fontsize=13, framealpha=0.85, 
                                           shadow=True, fancybox=True)
        legend.get_frame().set_facecolor('#0a0e27')
        legend.get_frame().set_edgecolor('#00d4ff')
        legend.get_frame().set_linewidth(2)
        for text in legend.get_texts():
            text.set_color('#ffffff')
        
        # 优化布局以充分利用图表区域
        self.fig_actual_load.subplots_adjust(
            left=0.07, bottom=0.08, right=0.98, top=0.95,
            wspace=0.12, hspace=0.12
        )
        
        self.canvas_actual_load.draw()

    def cap_y_axis(self, ax, data_arrays):
        """限制纵向高度不超过数据最高的1.2倍"""
        y_max = None
        y_min = None
        for data in data_arrays:
            if data is None:
                continue
            data_array = np.asarray(data, dtype=float)
            if data_array.size == 0:
                continue
            line_max = np.nanmax(data_array)
            line_min = np.nanmin(data_array)
            y_max = line_max if y_max is None else max(y_max, line_max)
            y_min = line_min if y_min is None else min(y_min, line_min)
        if y_max is not None and y_max > 0:
            y_upper = y_max * 1.2
            y_lower = y_min if y_min is not None else 0.0
            if y_lower >= y_upper:
                y_lower = y_upper * 0.8
            ax.set_ylim(y_lower, y_upper)

    def redraw_segment_lines(self):
        """重新绘制分割线，确保它们在图表操作后保持显示"""
        if not hasattr(self, 'segment_points') or not self.segment_points:
            return
        
        # 清除旧的分割线和文字对象
        for line in self.segment_lines:
            try:
                line.remove()
            except:
                pass
        for text in self.segment_texts:
            try:
                text.remove()
            except:
                pass
        
        self.segment_lines.clear()
        self.segment_texts.clear()
        
        # 重新绘制分割线
        for i, x_pos in enumerate(self.segment_points):
            # 绘制分割线
            line = self.ax_actual_load.axvline(x=x_pos, color='black', linestyle='--', 
                                             linewidth=2, alpha=0.7)
            self.segment_lines.append(line)
            
            # 添加标签
            y_min, y_max = self.ax_actual_load.get_ylim()
            text_obj = self.ax_actual_load.text(x_pos, y_max * 0.9, f'分割点{i+1}', 
                                               rotation=90, ha='right', va='top', 
                                               color='black', fontweight='bold')
            self.segment_texts.append(text_obj)

    def switch_data_source(self):
        """切换数据源"""
        if hasattr(self, 'actual_load_input_path') and self.actual_load_input_path.get():
            # 清空当前数据
            self.actual_load_data = None

            self.filtered_data = None  # 兼容
            self.is_filtered = False
            self.actual_load_intervals = None
            self.actual_load_interval_values = None
            
            # 重新加载数据
            self.load_actual_load_data()
        else:
            # 只是更新显示
            self.show_actual_load_initial_message()

    def butter_lowpass_filter(self, data, cutoff, fs, order=4):
        """应用巴特沃斯低通滤波器"""
        try:
            nyq = 0.5 * fs  # 奈奎斯特频率
            normal_cutoff = cutoff / nyq
            b, a = butter(order, normal_cutoff, btype='low', analog=False)
            y = filtfilt(b, a, data)
            return y
        except ImportError:
            # 如果scipy不可用，使用简单的移动平均滤波
            messagebox.showwarning("警告", "未找到SciPy库，使用简单的移动平均滤波")
            window_size = int(1 / cutoff)
            if window_size < 3:
                window_size = 3
            return np.convolve(data, np.ones(window_size)/window_size, mode='same')

    def apply_filter(self):
        """应用低通滤波器到数据"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        try:
            # 获取滤波参数
            cutoff = self.cutoff_freq.get()
            order = self.filter_order.get()
            
            # 验证参数
            if cutoff <= 0 or cutoff > 0.5:
                messagebox.showerror("参数错误", "截止频率必须在0.01到0.5之间")
                return
            
            if order < 1 or order > 10:
                messagebox.showerror("参数错误", "滤波器阶数必须在1到10之间")
                return
            
            # 将数据转换为numpy数组以便处理
            data_array = np.asarray(self.actual_load_data)
            
            # 应用低通滤波器
            fs = 1.0  # 采样频率，假设为1Hz
            filtered_data = self.butter_lowpass_filter(data_array, cutoff, fs, order)
            
            # 保存滤波后的数据
            self.filtered_data = filtered_data
            self.is_filtered = True
            
            # 更新图表显示滤波后的数据
            self.ax_actual_load.clear()
            
            # 绘制原始数据和滤波后的数据
            self.ax_actual_load.plot(self.actual_load_x_positions, data_array, 
                                    'b-', linewidth=0.5, alpha=0.7, label='原始数据')
            self.ax_actual_load.plot(self.actual_load_x_positions, filtered_data, 
                                    'r-', linewidth=1.5, label='滤波后数据')
            
            # 根据数据源设置标题和标签
            data_source = self.data_source_var.get()
            if data_source == "current":
                title = f'负载电流数据 (滤波后)'
                ylabel = '电流值'
            elif data_source == "vgpro_power":
                title = f'VGpro功率数据 (滤波后)'
                ylabel = '功率值'
            else:  # huazhong_power
                title = f'华中模块功率数据 (滤波后)'
                ylabel = '功率值'
            
            self.ax_actual_load.set_title(title)
            self.ax_actual_load.set_xlabel('程序行号位置')
            self.ax_actual_load.set_ylabel(ylabel)
            
            # 设置横轴刻度标签
            unique_line_numbers = self.actual_load_unique_line_numbers
            if len(unique_line_numbers) == 1:
                n = unique_line_numbers[0]
                self.ax_actual_load.set_xticks([n, n+0.5, n+1])
                self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"])
            elif len(unique_line_numbers) > 20:
                step = max(1, len(unique_line_numbers) // 10)
                tick_positions = range(0, len(unique_line_numbers), step)
                tick_labels = [str(unique_line_numbers[i]) for i in tick_positions]
                self.ax_actual_load.set_xticks(tick_positions)
                self.ax_actual_load.set_xticklabels(tick_labels, rotation=45)
            else:
                self.ax_actual_load.set_xticks(range(len(unique_line_numbers)))
                self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], rotation=45)
            
            # 使用更美观的网格样式
            self.ax_actual_load.grid(True, linestyle=':', alpha=0.4, linewidth=0.8, color='gray')
            self.ax_actual_load.legend(loc='upper right', fontsize=9, framealpha=0.9, shadow=True)
            
            # 优化布局
            self.fig_actual_load.subplots_adjust(
                left=0.08, bottom=0.10, right=0.96, top=0.94,
                wspace=0.15, hspace=0.15
            )
            
            self.canvas_actual_load.draw()
            
            # 更新状态
            self.status_var_actual_load.set(f"滤波应用成功! 截止频率: {cutoff}, 阶数: {order}")
            
        except Exception as e:
            messagebox.showerror("滤波错误", f"应用滤波时发生错误:\n{str(e)}")
            self.status_var_actual_load.set("滤波失败")


    





    def browse_actual_load_file(self):
        """浏览实际负载分析输入文件"""
        file_path = filedialog.askopenfilename(
            title="选择数据文件",
            filetypes=(("文本文件", "*.txt"), ("Excel文件", "*.xlsx"), ("CSV文件", "*.csv"), ("所有文件", "*.*"))
        )
        if file_path:
            self.actual_load_input_path.set(file_path)
            self.status_var_actual_load.set(f"已选择文件: {os.path.basename(file_path)}")

    def show_actual_load_initial_message(self):
        """显示初始提示信息"""
        self.ax_actual_load.clear()
        
        # 确保图表填充整个区域
        self.ax_actual_load.set_xlim(0, 1)
        self.ax_actual_load.set_ylim(0, 1)
        
        self.ax_actual_load.text(0.5, 0.5, "请选择数据文件并运行分析", 
                                horizontalalignment='center', 
                                verticalalignment='center',
                                fontsize=16,
                                color='gray',
                                weight='bold')
        self.ax_actual_load.axis('off')
        
        # 确保图表布局优化
        self.fig_actual_load.subplots_adjust(
            left=0.08, bottom=0.10, right=0.96, top=0.94
        )
        
        self.canvas_actual_load.draw()
        
        # 清空结果文本
        self.actual_load_result_text.delete(1.0, tk.END)
        self.actual_load_result_text.insert(tk.END, "分析结果将显示在这里...")

    def load_actual_load_data(self):
        """加载实际负载数据"""

        self.filtered_data = None  # 兼容
        self.is_filtered = False
        file_path = self.actual_load_input_path.get()
        
        if not file_path:
            messagebox.showerror("错误", "请选择输入文件")
            return
        
        if not os.path.exists(file_path):
            messagebox.showerror("错误", f"文件不存在: {file_path}")
            return
        
        try:
            # 根据文件扩展名选择不同的读取方式
            if file_path.endswith('.xlsx'):
                # 读取Excel文件
                df = pd.read_excel(file_path, header=None)
                
                # 将DataFrame转换为字符串列表，模拟文本文件的行
                content_lines = []
                for i in range(len(df)):
                    row = df.iloc[i].values
                    # 将行转换为字符串，用制表符分隔
                    line = '\t'.join([str(x) for x in row if pd.notna(x)])
                    content_lines.append(line)
                
                content = '\n'.join(content_lines)
            elif file_path.endswith('.csv'):
                # 读取CSV文件 - 改进CSV文件解析
                try:
                    # 尝试自动检测分隔符
                    with open(file_path, 'r', encoding='utf-8') as f:
                        sample = f.read(4096)
                    
                    # 检测分隔符
                    if ',' in sample and '\t' not in sample:
                        sep = ','
                    elif '\t' in sample and ',' not in sample:
                        sep = '\t'
                    else:
                        # 如果都有，优先使用逗号
                        sep = ','
                    
                    # 读取CSV文件
                    df = pd.read_csv(file_path, sep=sep, header=None, engine='python')
                    
                    # 将DataFrame转换为字符串列表
                    content_lines = []
                    for i in range(len(df)):
                        row = df.iloc[i].values
                        # 将行转换为字符串，使用检测到的分隔符
                        line = sep.join([str(x) for x in row if pd.notna(x)])
                        content_lines.append(line)
                    
                    content = '\n'.join(content_lines)
                except Exception as e:
                    # 如果读取失败，尝试使用原始文本方式
                    encoding_choice = self.actual_load_encoding_var.get()
                    if encoding_choice == "auto":
                        encoding = self.detect_file_encoding(file_path)
                    else:
                        encoding = encoding_choice
                    
                    with open(file_path, 'r', encoding=encoding) as f:
                        content = f.read()
            else:
                # 确定文件编码
                encoding_choice = self.actual_load_encoding_var.get()
                if encoding_choice == "auto":
                    encoding = self.detect_file_encoding(file_path)
                else:
                    encoding = encoding_choice
                
                # 读取文本文件内容
                with open(file_path, 'r', encoding=encoding) as f:
                    content = f.read()
            
            # 按行分割内容
            lines = content.split('\n')
            
            # 收集ChannelInfo行和ChannelData行
            channel_info_lines = []
            channel_data_lines = []
            
            for line in lines:
                line = line.strip()
                if line.startswith("<ChannelInfo>"):
                    channel_info_lines.append(line)
                elif line.startswith("<ChannelData>"):
                    channel_data_lines.append(line)
            
            if not channel_info_lines or not channel_data_lines:
                messagebox.showerror("错误", "文件格式不正确，缺少必要的标签")
                return
            
            # 根据选择的数据源确定要提取的列
            data_source = self.data_source_var.get()
            
            # 查找对应数据列的位置
            target_col = -1
            line_number_col = -1
            
            for i, line in enumerate(channel_info_lines):
                # 分割ChannelInfo行的字段
                if file_path.endswith('.csv'):
                    # CSV文件使用逗号分隔
                    fields = line.split(',')
                else:
                    # 其他文件使用制表符分隔
                    fields = line.split('\t')
                
                # 第三个字段是通道名称（索引3），第六个字段是寄存器编号（索引6）
                if len(fields) > 5:
                    channel_name = fields[3].strip('<> ')
                    register_number = fields[6].strip('<> ')
                    
                    if data_source == "current" and channel_name == '负载电流':
                        target_col = i
                    elif data_source == "vgpro_power" and register_number == '432':
                        target_col = i
                    elif data_source == "huazhong_power" and register_number == '108':
                        target_col = i
                    elif channel_name == '程序行号':
                        line_number_col = i
            
            if target_col == -1 or line_number_col == -1:
                messagebox.showerror("错误", f"文件中未找到{self.get_data_source_name()}或程序行号信息")
                return
            
            # 解析数据
            self.actual_load_data = []
            self.actual_load_line_numbers = []
            self.actual_load_point_indices = []  # 记录每个数据点在其行内的索引
            
            # 记录每行的数据点数量
            line_point_counts = {}
            
            for line in channel_data_lines:
                if file_path.endswith('.csv'):
                    # CSV文件使用逗号分隔
                    values = line.split(',')
                else:
                    # 其他文件使用制表符分隔
                    values = line.split('\t')
                    
                if len(values) > max(target_col, line_number_col):
                    try:
                        # ChannelData行的第一个字段是<ChannelData>标签，数据从第二个字段开始
                        # 所以列索引需要+1
                        target_value = float(values[target_col + 1])
                        line_number = float(values[line_number_col + 1])
                        self.actual_load_data.append(target_value)
                        self.actual_load_line_numbers.append(line_number)
                        
                        # 记录行内索引
                        if line_number not in line_point_counts:
                            line_point_counts[line_number] = 0
                        else:
                            line_point_counts[line_number] += 1
                        
                        self.actual_load_point_indices.append(line_point_counts[line_number])
                    except (ValueError, IndexError):
                        continue
            
            if not self.actual_load_data:
                messagebox.showerror("错误", "未能提取有效数据")
                return
            
            # 显示数据摘要
            self.status_var_actual_load.set(f"成功加载{self.get_data_source_name()}数据: {len(self.actual_load_data)}个数据点")
            self.actual_load_result_text.delete(1.0, tk.END)
            self.actual_load_result_text.insert(tk.END, f"数据文件: {os.path.basename(file_path)}\n")
            if not file_path.endswith('.xlsx') and not file_path.endswith('.csv'):
                self.actual_load_result_text.insert(tk.END, f"文件编码: {encoding}\n")
            self.actual_load_result_text.insert(tk.END, f"数据点数: {len(self.actual_load_data)}\n")
            self.actual_load_result_text.insert(tk.END, f"{self.get_data_source_name()}范围: {min(self.actual_load_data):.2f} - {max(self.actual_load_data):.2f}\n")
            self.actual_load_result_text.insert(tk.END, f"程序行号范围: {min(self.actual_load_line_numbers):.0f} - {max(self.actual_load_line_numbers):.0f}\n")
            
            # 计算x轴位置
            unique_line_numbers = sorted(set(self.actual_load_line_numbers))
            self.actual_load_x_positions = []
            
            if len(unique_line_numbers) == 1:
                # 所有行号相同，均匀分布在[N, N+1)区间内
                n = unique_line_numbers[0]
                total_points = len(self.actual_load_line_numbers)
                for i in range(total_points):
                    # 在[N, N+1)区间内均匀分布
                    self.actual_load_x_positions.append(n + i / total_points)
            else:
                # 为每个数据点计算唯一的x坐标: 行号 + 行内索引/行内总数
                # 统计每个行号的总点数
                line_point_counts = {}
                for ln in self.actual_load_line_numbers:
                    line_point_counts[ln] = line_point_counts.get(ln, 0) + 1
                
                # 为每个数据点计算x坐标
                for i in range(len(self.actual_load_line_numbers)):
                    ln = self.actual_load_line_numbers[i]
                    pt_idx = self.actual_load_point_indices[i]
                    total_pts = line_point_counts[ln]
                    
                    # x坐标 = 行号 + (行内索引 / 行内总数)
                    x_pos = ln + pt_idx / total_pts
                    self.actual_load_x_positions.append(x_pos)
            
            # 绘制原始数据预览 - 改为折线图
            self.ax_actual_load.clear()
            
            # 使用plot而不是scatter，按顺序连接点成线
            self.ax_actual_load.plot(self.actual_load_x_positions, self.actual_load_data, 'b-', linewidth=1.0)
            
            # 根据数据源设置标题和标签
            data_source = self.data_source_var.get()
            if data_source == "current":
                title = '负载电流数据预览'
                ylabel = '电流 (A)'
            elif data_source == "vgpro_power":
                title = 'VGpro功率数据预览'
                ylabel = '功率'
            else:  # huazhong_power
                title = '华中模块功率数据预览'
                ylabel = '功率'
            
            self.ax_actual_load.set_title(title)
            self.ax_actual_load.set_xlabel('程序行号位置')
            self.ax_actual_load.set_ylabel(ylabel)
            
            # 设置横轴刻度标签
            if len(unique_line_numbers) == 1:
                # 只有一个行号，显示该行号和下一个行号
                n = unique_line_numbers[0]
                self.ax_actual_load.set_xticks([n, n+0.5, n+1])
                self.ax_actual_load.set_xticklabels([f"{n:.0f}", f"{n+0.5:.1f}", f"{n+1:.0f}"])
            elif len(unique_line_numbers) > 20:
                # 如果行号太多，只显示部分标签
                step = max(1, len(unique_line_numbers) // 10)
                tick_positions = range(0, len(unique_line_numbers), step)
                tick_labels = [str(unique_line_numbers[i]) for i in tick_positions]
                self.ax_actual_load.set_xticks(tick_positions)
                self.ax_actual_load.set_xticklabels(tick_labels, rotation=45)
            else:
                self.ax_actual_load.set_xticks(range(len(unique_line_numbers)))
                self.ax_actual_load.set_xticklabels([str(ln) for ln in unique_line_numbers], rotation=45)
            
            self.ax_actual_load.grid(True, linestyle='--', alpha=0.7)
            self.canvas_actual_load.draw()
            
            # 设置图表交互功能
            self.setup_chart_interactions()
            
            # 保存映射关系供后续使用
            self.actual_load_unique_line_numbers = unique_line_numbers
            
        except Exception as e:
            messagebox.showerror("加载错误", f"加载数据时发生错误:\n{str(e)}")
            self.status_var_actual_load.set("加载失败")

    def get_data_source_name(self):
        """获取当前数据源的名称"""
        data_source = self.data_source_var.get()
        if data_source == "current":
            return "负载电流"
        elif data_source == "vgpro_power":
            return "VGpro功率"
        else:  # huazhong_power
            return "华中模块功率"

    def analyze_actual_load_data(self):
        """分析实际负载数据"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        try:
            min_len = self.actual_load_min_length.get()
            if min_len < 1:
                messagebox.showwarning("参数错误", "最小区间长度必须大于0")
                return
            
            # 获取波动阈值
            threshold = self.actual_current_threshold.get()
            absolute_threshold = self.absolute_threshold.get()
            
            # 确定使用原始数据还是滤波数据
            if self.is_filtered and self.filtered_data is not None:
                analysis_data = self.filtered_data
                data_type = "滤波"
            else:
                analysis_data = self.actual_load_data
                data_type = "原始"
            
            # 应用稳态区间划分算法 - 修改为按照程序行号顺序
            # 首先按照程序行号对数据进行排序
            sorted_indices = np.argsort(self.actual_load_line_numbers)
            sorted_values = np.asarray(analysis_data)[sorted_indices]
            sorted_line_numbers = np.asarray(self.actual_load_line_numbers)[sorted_indices]
            
            # 在排序后的数据上应用稳态区间划分
            raw_intervals = self.find_steady_state_intervals(
                sorted_values, 
                min_len, 
                threshold,
                absolute_threshold,
                adaptive=False,  # 禁用自适应，严格按照用户设置的阈值
                respect_user_thresholds=True  # 尊重用户设置的阈值
            )
            # 新增：再次检查并处理区间重叠（确保双重保护）
            intervals = self.adjust_overlapping_intervals(raw_intervals, overlap_tolerance=10)
            
            # 将区间索引转换回原始数据索引
            original_intervals = []
            for start_idx, end_idx in intervals:
                original_start = sorted_indices[start_idx]
                original_end = sorted_indices[end_idx]
                original_intervals.append((original_start, original_end))
            
            # 确保区间按照程序行号顺序排列
            original_intervals.sort(key=lambda x: self.actual_load_line_numbers[x[0]])
            
            if not original_intervals:
                messagebox.showinfo("结果", "未找到稳态区间")
                self.status_var_actual_load.set("未找到稳态区间")
                return
            
            # 根据复选框决定是否缩减区间
            reduce_interval = self.reduce_interval_actual_load.get()
            self.actual_load_intervals = []
            for (start_idx, end_idx) in original_intervals:
                if reduce_interval and end_idx - start_idx >= 2:
                    adjusted_start = start_idx + 1
                    adjusted_end = end_idx - 1
                    self.actual_load_intervals.append((adjusted_start, adjusted_end))
                else:
                    self.actual_load_intervals.append((start_idx, end_idx))
            
            # 保存当前区间供手动合并使用
            self.current_intervals = self.actual_load_intervals.copy()
            
            # 更新结果文本
            self.update_interval_display(data_type, reduce_interval)
            
            # 绘制稳态区间
            self.plot_steady_intervals(data_type)
            
            # 更新状态
            reduce_status = "启用" if reduce_interval else "禁用"
            self.status_var_actual_load.set(
                f"分析完成! 使用{data_type}数据找到 {len(self.actual_load_intervals)} 个稳态区间 " +
                f"(区间缩减: {reduce_status})"
            )
            
        except Exception as e:
            messagebox.showerror("分析错误", f"分析过程中发生错误:\n{str(e)}")
            self.status_var_actual_load.set("分析失败")

    def save_actual_load_results(self):
        """保存实际负载分析结果"""
        if not hasattr(self, 'actual_load_intervals') or not self.actual_load_intervals:
            messagebox.showwarning("无结果", "请先运行分析")
            return
        
        # 选择保存目录
        save_dir = filedialog.askdirectory(
            title="选择结果保存目录",
            mustexist=False
        )
        
        if not save_dir:
            return  # 用户取消选择
        
        try:
            # 创建目录（如果不存在）
            os.makedirs(save_dir, exist_ok=True)
            
            # 保存图表 - 同时保存高清PNG和矢量SVG格式
            base_name = f"actual_{self.data_source_var.get()}_steady_intervals"
            png_path = os.path.join(save_dir, f"{base_name}.png")
            svg_path = os.path.join(save_dir, f"{base_name}.svg")
            self.fig_actual_load.savefig(png_path, dpi=600, bbox_inches='tight', format='png')
            self.fig_actual_load.savefig(svg_path, bbox_inches='tight', format='svg')
            
            # 保存区间数据
            txt_path = os.path.join(save_dir, f"actual_{self.data_source_var.get()}_steady_intervals.txt")
            with open(txt_path, 'w', encoding='utf-8') as f:
                # 添加数据类型信息
                if self.is_filtered and self.filtered_data is not None:
                    f.write("# 使用滤波数据进行分析\n")
                else:
                    f.write("# 使用原始数据进行分析\n")
                
                # 添加区间缩减信息
                reduce_status = "启用" if self.reduce_interval_actual_load.get() else "禁用"
                f.write(f"# 区间缩减: {reduce_status}\n")
                
                f.write("# 起始索引\t结束索引\t起始程序行号.点索引\t结束程序行号.点索引\t长度(点)\n")
                for i, (start_idx, end_idx) in enumerate(self.actual_load_intervals):
                    # 获取程序行号和行内索引
                    start_ln = self.actual_load_line_numbers[start_idx]
                    start_point_idx = self.actual_load_point_indices[start_idx]
                    end_ln = self.actual_load_line_numbers[end_idx]
                    end_point_idx = self.actual_load_point_indices[end_idx]
                    
                    length_points = end_idx - start_idx + 1
                    if self.actual_load_interval_values is None:
                        self.actual_load_interval_values = []
                    avg_value = self.actual_load_interval_values[i] if i < len(self.actual_load_interval_values) else 0.0
                    
                    # 使用新格式保存区间
                    f.write(f"{start_idx}\t{end_idx}\t{start_ln:.0f}.{start_point_idx}\t{end_ln:.0f}.{end_point_idx}\t{length_points}\n")
            
            self.status_var_actual_load.set(f"结果已保存到: {save_dir}")
            messagebox.showinfo("保存成功", 
                            f"分析结果已保存到:\n{save_dir}\n\n" +
                            f"• 稳态区间图: {os.path.basename(fig_path)}\n" +
                            f"• 区间数据文件: {os.path.basename(txt_path)}")
            
        except Exception as e:
            messagebox.showerror("保存错误", f"保存结果时发生错误:\n{str(e)}")

    def optimize_processing(self):
        """优化处理性能"""
        # 禁用matplotlib的交互模式
        plt.ioff()
        
        # 减少pandas内存使用
        if 'pandas' in sys.modules:
            pd.options.mode.chained_assignment = None  # 禁用链式赋值警告
            pd.options.display.float_format = '{:.6f}'.format
        
        # 优化matplotlib配置
        matplotlib.rcParams['path.simplify'] = True
        matplotlib.rcParams['path.simplify_threshold'] = 1.0
        matplotlib.rcParams['agg.path.chunksize'] = 10000
    
    def init_figures(self):
        """初始化图表 - 科技感深色主题，自适应全屏显示"""
        # 获取实际窗口大小
        self.root.update_idletasks()  # 确保获取最新的窗口大小
        window_width = self.root.winfo_width()
        window_height = self.root.winfo_height()
        
        # 计算图表尺寸 - 更大的尺寸确保内容完整显示
        # 使用更激进的比例以充分利用空间
        fig_width = max(14, window_width * 0.012)  # 增大到14英寸起步
        fig_height = max(8, window_height * 0.008)  # 增大到8英寸起步
        
        # 数据处理标签页的图表 - 科技感深色主题
        self.fig_data, self.ax_data = plt.subplots(figsize=(fig_width, fig_height), dpi=100)
        
        # 设置白色背景
        self.fig_data.patch.set_facecolor('white')
        self.ax_data.set_facecolor('white')
        
        # 优化子图边距以居中对称显示，数据占2/3以上
        self.fig_data.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
        
        # ⚠️ data_figure_frame 使用 grid 布局，这里必须用 grid，不能 pack
        # 先清空占位内容，避免 grid/pack 混用报错（必须在创建新画布之前清空）
        try:
            for w in self.data_figure_frame.winfo_children():
                w.destroy()
            self.data_figure_frame.grid_rowconfigure(0, weight=1)
            self.data_figure_frame.grid_columnconfigure(0, weight=1)
        except Exception:
            pass
        
        # 创建画布（在清空旧控件之后）
        self.canvas_data = FigureCanvasTkAgg(self.fig_data, master=self.data_figure_frame)
        canvas_widget = self.canvas_data.get_tk_widget()
        canvas_widget.grid(row=0, column=0, sticky="nsew")
        canvas_widget.configure(relief=tk.FLAT, bd=0)

        # 让图表随预览区域变化实时放缩（防抖）
        try:
            canvas_widget.bind('<Configure>', self._on_preview_canvas_configure)
        except Exception:
            pass
        
        # 为数据处理图表添加鼠标滚轮横向缩放功能
        self.canvas_data.mpl_connect('scroll_event', self.on_data_scroll_zoom)
        
        # 显示初始提示
        self.show_initial_message()
    
    def show_initial_message(self):
        """显示初始提示信息"""
        self.ax_data.clear()
        self.ax_data.set_facecolor('white')
        self.ax_data.set_xlim(0, 1)
        self.ax_data.set_ylim(0, 1)
        self.ax_data.text(
            0.5,
            0.5,
            '请选择txt文件并点击"一键处理"',
            horizontalalignment='center',
            verticalalignment='center',
            transform=self.ax_data.transAxes,
            fontsize=20,
            fontweight='bold',
            color='#333333'
        )
        self.ax_data.set_anchor('C')
        self.ax_data.axis('off')
        self.canvas_data.draw_idle()
        
    def create_data_processing_tab(self):
        """工艺信息分析页面：固定布局（无滚动条）+ 随窗口放缩铺满 + 可调分区 + 参数可折叠"""
        # 页面总体：0=主体(可伸缩)，1=进度条，2=状态栏
        self.data_processing_tab.grid_columnconfigure(0, weight=1)
        self.data_processing_tab.grid_rowconfigure(0, weight=1)
        self.data_processing_tab.grid_rowconfigure(1, weight=0)
        self.data_processing_tab.grid_rowconfigure(2, weight=0)

        # 上下可调分区（上：输入/参数/按钮；下：图表预览）
        paned = ttk.PanedWindow(self.data_processing_tab, orient=tk.VERTICAL)
        paned.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        self._data_paned = paned  # 保存引用以便后续调整sash位置

        controls = ttk.Frame(paned)
        preview = ttk.Frame(paned)
        self._data_controls = controls  # 保存引用

        paned.add(controls, weight=0)   # 控件区默认较小，可被用户拖动调整
        paned.add(preview, weight=1)    # 预览区吃掉剩余空间

        # ===== 控件区 =====
        controls.grid_columnconfigure(0, weight=1)

        # 输入文件
        input_frame = ttk.LabelFrame(controls, text="📁 输入设置", padding=10, style='Tech.TLabelframe')
        input_frame.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        input_frame.grid_columnconfigure(1, weight=1)

        ttk.Label(input_frame, text="输入文件:", font=('Microsoft YaHei UI', 10)).grid(row=0, column=0, sticky="w")
        data_file_entry = ttk.Entry(input_frame, textvariable=self.input_file_path, font=('Consolas', 10))
        data_file_entry.grid(row=0, column=1, padx=6, sticky="ew")
        ttk.Button(input_frame, text="🔍 浏览...", command=self.browse_input_file, style='Tech.TButton').grid(row=0, column=2, padx=(0, 2))

        # 参数折叠开关（默认折叠）
        if not hasattr(self, '_show_params_var'):
            self._show_params_var = tk.BooleanVar(value=False)

        toggle_row = ttk.Frame(controls)
        toggle_row.grid(row=1, column=0, sticky="ew", pady=(0, 4))
        toggle_row.grid_columnconfigure(1, weight=1)

        if not hasattr(self, '_param_toggle_text'):
            self._param_toggle_text = tk.StringVar()

        def _update_param_toggle_text():
            self._param_toggle_text.set("▼ 计算参数" if self._show_params_var.get() else "▶ 计算参数")

        def _toggle_params():
            self._show_params_var.set(not self._show_params_var.get())
            if self._show_params_var.get():
                # 展开计算参数时：显示参数框，自动调整分割线位置
                param_frame.grid()
                # 延迟计算并调整sash位置，确保参数框完全显示
                def _adjust_sash():
                    try:
                        self._data_controls.update_idletasks()
                        # 获取控件区所需高度
                        required_height = self._data_controls.winfo_reqheight()
                        # 设置sash位置，使控件区完整显示
                        self._data_paned.sashpos(0, required_height + 5)
                    except Exception:
                        pass
                self.root.after(50, _adjust_sash)
            else:
                # 收起计算参数时：隐藏参数框，自动调整分割线位置
                param_frame.grid_remove()
                # 延迟调整sash位置，缩小控件区
                def _adjust_sash():
                    try:
                        self._data_controls.update_idletasks()
                        required_height = self._data_controls.winfo_reqheight()
                        self._data_paned.sashpos(0, required_height + 5)
                    except Exception:
                        pass
                self.root.after(50, _adjust_sash)
            _update_param_toggle_text()
            # 延迟调整图表大小以适应新布局
            self.root.after(100, self.adjust_figure_sizes)

        _update_param_toggle_text()
        ttk.Button(toggle_row, textvariable=self._param_toggle_text, command=_toggle_params, style='Tech.TButton').grid(row=0, column=0, sticky="w")
        ttk.Label(toggle_row, text="默认折叠：最大化也不溢出；需要时再展开", foreground="#666666",
                  font=('Microsoft YaHei UI', 9)).grid(row=0, column=1, sticky="w", padx=8)

        # 参数区（默认隐藏：grid_remove）
        param_frame = ttk.LabelFrame(controls, text="⚙️ 计算参数", padding=10, style='Tech.TLabelframe')
        param_frame.grid(row=2, column=0, sticky="ew", pady=(0, 6))

        # 机床原点（原工程里是在此处初始化）
        if not hasattr(self, 'origin_x'):
            self.origin_x = tk.DoubleVar(value=349.765)
        if not hasattr(self, 'origin_y'):
            self.origin_y = tk.DoubleVar(value=-10.205)
        if not hasattr(self, 'origin_z'):
            self.origin_z = tk.DoubleVar(value=-459.070)

                # Row 0：基准转速（用于无S指令时的默认转速）
        ttk.Label(param_frame, text="基准转速 (rpm):").grid(row=0, column=0, sticky="w")
        ttk.Entry(param_frame, textvariable=self.s_base, width=10).grid(row=0, column=1, padx=6, sticky="ew")
        ttk.Label(param_frame, text="(无 S 指令时采用该转速)", foreground="#666666").grid(row=0, column=2, columnspan=3, sticky="w")

        # Row 1：空载功率 P_idle
        ttk.Label(param_frame, text="空载功率 P_idle (W):").grid(row=1, column=0, sticky="w", pady=(2, 0))
        ttk.Entry(param_frame, textvariable=self.p_idle, width=10).grid(row=1, column=1, padx=6, sticky="ew", pady=(2, 0))

        # Row 2：空间加工阻抗系数 Z(s)
        ttk.Label(param_frame, text="阻抗系数 Z(s):").grid(row=2, column=0, sticky="w", pady=(2, 0))
        ttk.Entry(param_frame, textvariable=self.z_impedance, width=10).grid(row=2, column=1, padx=6, sticky="ew", pady=(2, 0))
        ttk.Label(param_frame, text="(单位: W/(mm³/s), P_pred = P_idle + Z(s)·MRR)", foreground="#666666").grid(
            row=2, column=2, columnspan=4, padx=(10, 0), sticky="w", pady=(2, 0)
        )

        # Row 3：额定功率 P_rated（可选硬约束）
        ttk.Label(param_frame, text="额定功率 P_rated (W):").grid(row=3, column=0, sticky="w", pady=(2, 0))
        ttk.Entry(param_frame, textvariable=self.p_rated, width=10).grid(row=3, column=1, padx=6, sticky="ew", pady=(2, 0))
        ttk.Label(param_frame, text="(0 表示不启用硬约束)", foreground="#666666").grid(row=3, column=2, columnspan=2, sticky="w", pady=(2, 0))

        # Row 4：机床原点

        ttk.Label(param_frame, text="机床原点:").grid(row=4, column=0, sticky="w", pady=(6, 0))
        ttk.Label(param_frame, text="X:").grid(row=4, column=1, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.origin_x, width=10).grid(row=4, column=2, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="Y:").grid(row=4, column=3, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.origin_y, width=10).grid(row=4, column=4, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="Z:").grid(row=4, column=5, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.origin_z, width=10).grid(row=4, column=6, padx=6, sticky="ew", pady=(6, 0))

        # Row 3：快移速度
        ttk.Label(param_frame, text="快速移动速度(mm/min):").grid(row=5, column=0, sticky="w", pady=(6, 0))
        ttk.Label(param_frame, text="XY平面:").grid(row=5, column=1, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.rapid_speed_xy, width=10).grid(row=5, column=2, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="Z方向:").grid(row=5, column=3, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.rapid_speed_z, width=10).grid(row=5, column=4, padx=6, sticky="ew", pady=(6, 0))

        # Row 4：材料信息
        ttk.Label(param_frame, text="刀具直径(mm):").grid(row=6, column=0, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.tool_diameter, width=10).grid(row=6, column=1, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="刀具材料:").grid(row=6, column=2, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.workpiece_material, width=18).grid(row=6, column=3, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="毛坯材料:").grid(row=6, column=4, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.blank_material, width=18).grid(row=6, column=5, padx=6, sticky="ew", pady=(6, 0))

        # Row 5：MRR稳态区间（用“√/×”明确表示，避免主题把勾画成×）
        ttk.Label(param_frame, text="MRR稳态区间划分:").grid(row=7, column=0, sticky="w", pady=(6, 0))

        if not hasattr(self, '_mrr_enable_btn_text'):
            self._mrr_enable_btn_text = tk.StringVar()

        def _sync_mrr_enable_btn():
            self._mrr_enable_btn_text.set("√ 启用" if self.enable_mrr_steady.get() else "× 启用")

        def _toggle_mrr_enable():
            self.enable_mrr_steady.set(not self.enable_mrr_steady.get())
            _sync_mrr_enable_btn()

        _sync_mrr_enable_btn()
        ttk.Button(param_frame, textvariable=self._mrr_enable_btn_text, command=_toggle_mrr_enable,
                   style='Tech.TButton').grid(row=7, column=1, sticky="w", pady=(6, 0))

        ttk.Label(param_frame, text="最小行程长度(mm):").grid(row=7, column=2, sticky="w", pady=(6, 0))
        ttk.Entry(param_frame, textvariable=self.mrr_min_length, width=10).grid(row=7, column=3, padx=6, sticky="ew", pady=(6, 0))
        ttk.Label(param_frame, text="(将MRR恒定的连续段划为稳态区间)", foreground="#666666").grid(row=7, column=4, columnspan=3, sticky="w", pady=(6, 0))

        # 让输入框列在窗口变化时能拉伸
        for c in range(7):
            if c in (1, 2, 3, 4, 5, 6):
                param_frame.grid_columnconfigure(c, weight=1)
            else:
                param_frame.grid_columnconfigure(c, weight=0)

        # 默认折叠
        if not self._show_params_var.get():
            param_frame.grid_remove()

        # 操作按钮（只保留一个“保存所有图表”）
        button_frame = ttk.Frame(controls)
        button_frame.grid(row=3, column=0, sticky="ew", pady=(0, 2))
        ttk.Button(button_frame, text="⚡ 一键处理", command=self.one_click_process, style='Primary.TButton').pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="💾 保存所有图表", command=lambda: self.save_all_plots(silent=False), style='Tech.TButton').pack(side=tk.LEFT)

        # ===== 预览区 =====
        preview.grid_columnconfigure(0, weight=1)
        preview.grid_rowconfigure(1, weight=1)

        nav_frame = ttk.Frame(preview)
        nav_frame.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        nav_frame.grid_columnconfigure(1, weight=1)

        self.prev_btn = ttk.Button(nav_frame, text="◀ 上一张", command=self.show_prev_figure, state=tk.DISABLED, style='Tech.TButton')
        self.prev_btn.grid(row=0, column=0, padx=(0, 6))

        self.figure_label = ttk.Label(nav_frame, text="", font=('Microsoft YaHei UI', 11, 'bold'), foreground='#0066cc')
        self.figure_label.grid(row=0, column=1, sticky="w")

        ttk.Label(nav_frame, text="快速选择:", font=('Microsoft YaHei UI', 10)).grid(row=0, column=2, padx=(6, 2), sticky="e")
        self.figure_selector_var = tk.StringVar()
        self.figure_selector = ttk.Combobox(nav_frame, textvariable=self.figure_selector_var, state="readonly", width=25, font=('Microsoft YaHei UI', 10))
        self.figure_selector.bind("<<ComboboxSelected>>", self.on_figure_selected)
        self.figure_selector.grid(row=0, column=3, padx=6, sticky="e")

        self.next_btn = ttk.Button(nav_frame, text="下一张 ▶", command=self.show_next_figure, state=tk.DISABLED, style='Tech.TButton')
        self.next_btn.grid(row=0, column=4, padx=(0, 6))

        # 预览容器：铺满剩余空间
        self.data_figure_frame = ttk.LabelFrame(preview, text="图表预览（滚轮：横向缩放；Ctrl+滚轮：纵向缩放）", padding=6, style='Tech.TLabelframe')
        self.data_figure_frame.grid(row=1, column=0, sticky="nsew")
        self.data_figure_frame.grid_rowconfigure(0, weight=1)
        self.data_figure_frame.grid_columnconfigure(0, weight=1)
        self.data_figure_frame.bind("<Configure>", self._on_preview_canvas_configure)

        # 初始化空画布占位
        placeholder = ttk.Label(self.data_figure_frame, text="请先选择输入文件并点击“一键处理”生成图表",
                                foreground="#666666", anchor="center")
        placeholder.grid(row=0, column=0, sticky="nsew")

        # ===== 进度条与状态栏 =====
        progress_bar = ttk.Progressbar(self.data_processing_tab, orient=tk.HORIZONTAL, length=100, mode='determinate')
        progress_bar.grid(row=1, column=0, sticky="ew", padx=8)
        self.data_progress_bar = progress_bar

        if not hasattr(self, 'status_var_data'):
            self.status_var_data = tk.StringVar(value="就绪")
        status_bar = ttk.Label(self.data_processing_tab, textvariable=self.status_var_data, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.grid(row=2, column=0, sticky="ew", padx=8, pady=(0, 6))

        # 初始化分割条位置：默认给图表区更多空间（同时允许用户拖动调整）
        def _init_sash():
            try:
                total_h = paned.winfo_height()
                if total_h <= 10:
                    return
                ctrl_h = int(total_h * 0.28)
                ctrl_h = max(160, min(ctrl_h, 320))
                paned.sashpos(0, ctrl_h)
            except Exception:
                pass

        self.root.after(60, _init_sash)

    def create_steady_state_tab(self):
        """创建稳态区间标签页界面"""
        # 创建主容器
        main_container = ttk.Frame(self.steady_state_tab)
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # 创建画布和滚动条
        canvas = tk.Canvas(main_container, highlightthickness=0)
        v_scrollbar = ttk.Scrollbar(main_container, orient="vertical", command=canvas.yview)
        h_scrollbar = ttk.Scrollbar(main_container, orient="horizontal", command=canvas.xview)
        
        # 创建内容框架
        scrollable_frame = ttk.Frame(canvas)
        
        # 配置滚动
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # 布局滚动条和画布
        canvas.grid(row=0, column=0, sticky="nsew")
        v_scrollbar.grid(row=0, column=1, sticky="ns")
        h_scrollbar.grid(row=1, column=0, sticky="ew")
        
        # 配置网格权重
        main_container.grid_rowconfigure(0, weight=1)
        main_container.grid_columnconfigure(0, weight=1)
        
        # 自适应画布窗口大小
        def configure_scroll_region(event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas_width = canvas.winfo_width()
            canvas_height = canvas.winfo_height()
            req_width = scrollable_frame.winfo_reqwidth()
            req_height = scrollable_frame.winfo_reqheight()
            new_w = max(canvas_width, req_width)
            new_h = max(canvas_height, req_height)
            canvas.itemconfig(canvas_window, width=new_w, height=new_h)
        
        canvas.bind('<Configure>', configure_scroll_region)
        scrollable_frame.bind('<Configure>', configure_scroll_region)
        
        # 绑定鼠标滚轮事件（支持多平台）
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
        
        # 主框架 - 保持原有的布局风格
        main_frame = ttk.Frame(scrollable_frame, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 输入文件选择
        input_frame = ttk.LabelFrame(main_frame, text="输入设置", padding="10")
        input_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(input_frame, text="输入文件:").grid(row=0, column=0, sticky=tk.W)
        self.steady_input_path = tk.StringVar(value=self.processed_file_path)
        steady_file_entry = ttk.Entry(input_frame, textvariable=self.steady_input_path)
        steady_file_entry.grid(row=0, column=1, padx=5, sticky=tk.EW)  # 使用sticky=EW自适应宽度
        ttk.Button(input_frame, text="浏览...", command=self.browse_steady_input_file).grid(row=0, column=2)
        
        # 配置列权重，使文件输入框可以自适应扩展
        input_frame.columnconfigure(1, weight=1)
        
        # 使用最新处理结果按钮
        ttk.Button(input_frame, text="使用最新处理结果", command=self.use_latest_processed_file).grid(row=0, column=3, padx=5)
        
        # 添加编码选择
        ttk.Label(input_frame, text="文件编码:").grid(row=1, column=0, sticky=tk.W, pady=(10, 0))
        encoding_frame = ttk.Frame(input_frame)
        encoding_frame.grid(row=1, column=1, sticky=tk.W, pady=(10, 0))
        
        encodings = ["auto (自动检测)", "utf-8", "gbk", "gb2312", "latin1", "iso-8859-1", "cp1252"]
        ttk.Radiobutton(encoding_frame, text=encodings[0], variable=self.encoding_var, value="auto").pack(side=tk.LEFT)
        ttk.Radiobutton(encoding_frame, text=encodings[1], variable=self.encoding_var, value="utf-8").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[2], variable=self.encoding_var, value="gbk").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[3], variable=self.encoding_var, value="gb2312").pack(side=tk.LEFT, padx=5)
        
        # 参数设置
        param_frame = ttk.LabelFrame(main_frame, text="分析参数", padding="10")
        param_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(param_frame, text="最小区间长度:").grid(row=0, column=0, sticky=tk.W)
        ttk.Entry(param_frame, textvariable=self.min_length, width=10).grid(row=0, column=1, padx=5, sticky=tk.W)
        
        ttk.Label(param_frame, text="(最小连续数据点数)").grid(row=0, column=2, padx=10, sticky=tk.W)
        
        # 添加波动阈值设置
        ttk.Label(param_frame, text="波动阈值:").grid(row=1, column=0, sticky=tk.W, pady=(10, 0))
        ttk.Entry(param_frame, textvariable=self.steady_threshold, width=10).grid(row=1, column=1, padx=5, sticky=tk.W)
        ttk.Label(param_frame, text="(例如: 0.2 表示20%波动)").grid(row=1, column=2, padx=10, sticky=tk.W)
        # 在参数设置区域添加绝对阈值输入
        ttk.Label(param_frame, text="绝对波动阈值(A):").grid(row=2, column=0, sticky=tk.W, pady=(10, 0))
        self.absolute_threshold = tk.DoubleVar(value=0.05)  # 添加这个实例变量
        ttk.Entry(param_frame, textvariable=self.absolute_threshold, width=10).grid(row=2, column=1, padx=5, sticky=tk.W)
        ttk.Label(param_frame, text="(例如: 0.05 表示0.05A绝对波动)").grid(row=2, column=2, padx=10, sticky=tk.W)

        # 添加是否缩减区间的复选框
        ttk.Label(param_frame, text="缩减区间边界:").grid(row=3, column=0, sticky=tk.W, pady=(10, 0))
        self.reduce_interval_steady = tk.BooleanVar(value=True)  # 默认缩减
        ttk.Checkbutton(param_frame, text="启用", variable=self.reduce_interval_steady).grid(row=3, column=1, sticky=tk.W)
        ttk.Label(param_frame, text="(禁用时将使用完整区间)").grid(row=3, column=2, padx=10, sticky=tk.W)

        # 按钮区域
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(pady=10)
        
        load_btn = ttk.Button(button_frame, text="加载数据", command=self.load_data)
        load_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        analyze_btn = ttk.Button(button_frame, text="运行分析", command=self.analyze_data)
        analyze_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        save_btn = ttk.Button(button_frame, text="保存结果", command=self.save_results)
        save_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        reset_view_btn = ttk.Button(button_frame, text="重置视图", command=self.reset_steady_chart_view)
        reset_view_btn.pack(side=tk.LEFT, padx=5, pady=5, ipadx=20, ipady=5)
        
        # 状态栏
        self.status_var_steady = tk.StringVar()
        self.status_var_steady.set("就绪")
        status_bar = ttk.Label(self.steady_state_tab, textvariable=self.status_var_steady, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 图表区域
        self.figure_frame = ttk.Frame(main_frame)  # 改为普通Frame
        self.figure_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # 结果显示区域
        result_frame = ttk.LabelFrame(main_frame, text="稳态区间详情", padding="10")
        result_frame.pack(fill=tk.X, pady=5)
        
        # 创建文本区域显示结果
        self.result_text = tk.Text(result_frame, height=8, wrap=tk.WORD)
        self.result_text.pack(fill=tk.BOTH, expand=True)
        scrollbar = ttk.Scrollbar(result_frame, command=self.result_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.result_text.config(yscrollcommand=scrollbar.set)

    def create_batch_processing_tab(self):
        """创建批量处理标签页界面"""
        # 创建主容器
        main_container = ttk.Frame(self.batch_processing_tab)
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # 创建画布和滚动条
        canvas = tk.Canvas(main_container, highlightthickness=0)
        v_scrollbar = ttk.Scrollbar(main_container, orient="vertical", command=canvas.yview)
        h_scrollbar = ttk.Scrollbar(main_container, orient="horizontal", command=canvas.xview)
        
        # 创建内容框架
        scrollable_frame = ttk.Frame(canvas)
        
        # 配置滚动
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # 布局滚动条和画布
        canvas.grid(row=0, column=0, sticky="nsew")
        v_scrollbar.grid(row=0, column=1, sticky="ns")
        h_scrollbar.grid(row=1, column=0, sticky="ew")
        
        # 配置网格权重
        main_container.grid_rowconfigure(0, weight=1)
        main_container.grid_columnconfigure(0, weight=1)
        
        # 自适应画布窗口大小
        def configure_scroll_region(event=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas_width = canvas.winfo_width()
            canvas_height = canvas.winfo_height()
            req_width = scrollable_frame.winfo_reqwidth()
            req_height = scrollable_frame.winfo_reqheight()
            new_w = max(canvas_width, req_width)
            new_h = max(canvas_height, req_height)
            canvas.itemconfig(canvas_window, width=new_w, height=new_h)
        
        canvas.bind('<Configure>', configure_scroll_region)
        scrollable_frame.bind('<Configure>', configure_scroll_region)
        
        # 绑定鼠标滚轮事件（支持多平台）
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
        
        # 主框架 - 保持原有的布局风格
        main_frame = ttk.Frame(scrollable_frame, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 文件选择区域
        file_frame = ttk.LabelFrame(main_frame, text="输入文件", padding="10")
        file_frame.pack(fill=tk.X, pady=5)
        
        # 文件列表框
        list_frame = ttk.Frame(file_frame)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.file_listbox = tk.Listbox(list_frame, height=8, yscrollcommand=scrollbar.set)
        self.file_listbox.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.file_listbox.yview)
        
        # 文件操作按钮
        btn_frame = ttk.Frame(file_frame)
        btn_frame.pack(fill=tk.X, pady=5)
        
        add_btn = ttk.Button(btn_frame, text="添加文件", command=self.add_batch_files)
        add_btn.pack(side=tk.LEFT, padx=5)
        
        remove_btn = ttk.Button(btn_frame, text="移除选中", command=self.remove_selected_files)
        remove_btn.pack(side=tk.LEFT, padx=5)
        
        clear_btn = ttk.Button(btn_frame, text="清空列表", command=self.clear_file_list)
        clear_btn.pack(side=tk.LEFT, padx=5)
        
        # 参数设置区域
        param_frame = ttk.LabelFrame(main_frame, text="参数设置", padding="10")
        param_frame.pack(fill=tk.X, pady=5)
        
        # 计算参数
        calc_frame = ttk.LabelFrame(param_frame, text="计算参数")
        calc_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 在原有参数下方添加机床原点设置（独占一行）
        ttk.Label(calc_frame, text="机床原点:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Label(calc_frame, text="X:").grid(row=2, column=1, sticky=tk.W)
        self.batch_origin_x = tk.DoubleVar(value=349.765)
        ttk.Entry(calc_frame, textvariable=self.batch_origin_x, width=10).grid(row=2, column=2, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="Y:").grid(row=2, column=3, sticky=tk.W)
        self.batch_origin_y = tk.DoubleVar(value=-10.205)
        ttk.Entry(calc_frame, textvariable=self.batch_origin_y, width=10).grid(row=2, column=4, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="Z:").grid(row=2, column=5, sticky=tk.W)
        self.batch_origin_z = tk.DoubleVar(value=-459.070)
        ttk.Entry(calc_frame, textvariable=self.batch_origin_z, width=10).grid(row=2, column=6, padx=5, sticky=tk.W)
        
        # 在机床原点下方添加快移速度设置
        ttk.Label(calc_frame, text="快速移动速度(mm/min):").grid(row=3, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Label(calc_frame, text="XY平面:").grid(row=3, column=1, sticky=tk.W)
        ttk.Entry(calc_frame, textvariable=self.batch_rapid_speed_xy, width=10).grid(row=3, column=2, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="Z方向:").grid(row=3, column=3, sticky=tk.W)
        ttk.Entry(calc_frame, textvariable=self.batch_rapid_speed_z, width=10).grid(row=3, column=4, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="基准转速 (rpm):").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        s_entry = ttk.Entry(calc_frame, textvariable=self.s_base, width=10)
        s_entry.grid(row=0, column=1, padx=5, pady=2, sticky=tk.W)
        
        ttk.Label(calc_frame, text="基准扭矩系数 K:").grid(row=0, column=2, sticky=tk.W, padx=5, pady=2)
        k_entry = ttk.Entry(calc_frame, textvariable=self.k_base, width=10)
        k_entry.grid(row=0, column=3, padx=5, pady=2, sticky=tk.W)
        
        ttk.Label(calc_frame, text="电流系数 K':").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        k_prime_entry = ttk.Entry(calc_frame, textvariable=self.k_prime, width=10)
        k_prime_entry.grid(row=1, column=1, padx=5, pady=2, sticky=tk.W)
        
        # 在原有参数下方添加材料信息
        ttk.Label(calc_frame, text="刀具直径(mm):").grid(row=4, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(calc_frame, textvariable=self.batch_tool_diameter, width=10).grid(row=4, column=1, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="刀具材料:").grid(row=4, column=2, sticky=tk.W, padx=5)
        ttk.Entry(calc_frame, textvariable=self.batch_workpiece_material, width=15).grid(row=4, column=3, padx=5, sticky=tk.W)
        
        ttk.Label(calc_frame, text="毛坯材料:").grid(row=4, column=4, sticky=tk.W, padx=5)
        ttk.Entry(calc_frame, textvariable=self.batch_blank_material, width=15).grid(row=4, column=5, padx=5, sticky=tk.W)
        
        # 分析参数
        analysis_frame = ttk.LabelFrame(param_frame, text="分析参数")
        analysis_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(analysis_frame, text="最小区间长度:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        min_length_entry = ttk.Entry(analysis_frame, textvariable=self.min_length, width=10)
        min_length_entry.grid(row=0, column=1, padx=5, pady=2, sticky=tk.W)
        
        ttk.Label(analysis_frame, text="(最小连续数据点数)").grid(row=0, column=2, padx=5, pady=2, sticky=tk.W)
        
        # 添加波动阈值设置
        ttk.Label(analysis_frame, text="波动阈值:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        ttk.Entry(analysis_frame, textvariable=self.batch_threshold, width=10).grid(row=1, column=1, padx=5, pady=2, sticky=tk.W)
        ttk.Label(analysis_frame, text="(例如: 0.2 表示20%波动)").grid(row=1, column=2, padx=5, pady=2, sticky=tk.W)
        
        # 文件编码
        encoding_frame = ttk.LabelFrame(param_frame, text="文件编码")
        encoding_frame.pack(fill=tk.X, padx=5, pady=5)
        
        encodings = ["auto (自动检测)", "utf-8", "gbk", "gb2312"]
        ttk.Radiobutton(encoding_frame, text=encodings[0], variable=self.encoding_var, value="auto").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[1], variable=self.encoding_var, value="utf-8").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[2], variable=self.encoding_var, value="gbk").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(encoding_frame, text=encodings[3], variable=self.encoding_var, value="gb2312").pack(side=tk.LEFT, padx=5)
        
        # 输出设置
        output_frame = ttk.LabelFrame(main_frame, text="输出设置", padding="10")
        output_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(output_frame, text="输出目录:").grid(row=0, column=0, sticky=tk.W)
        self.output_dir_var = tk.StringVar()
        output_entry = ttk.Entry(output_frame, textvariable=self.output_dir_var, width=70)
        output_entry.grid(row=0, column=1, padx=5, sticky=tk.W)
        ttk.Button(output_frame, text="浏览...", command=self.browse_output_dir).grid(row=0, column=2)
        
        # 处理按钮
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(pady=10)
        
        process_btn = ttk.Button(button_frame, text="开始批量处理", command=self.batch_process_files, style="Accent.TButton")
        process_btn.pack(padx=5, pady=5, ipadx=30, ipady=5)
        
        # 状态栏
        self.status_var_batch = tk.StringVar()
        self.status_var_batch.set("就绪")
        status_bar = ttk.Label(self.batch_processing_tab, textvariable=self.status_var_batch, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 进度条
        self.batch_progress_var = tk.DoubleVar()
        progress_bar = ttk.Progressbar(self.batch_processing_tab, variable=self.batch_progress_var, maximum=100, mode='determinate')
        progress_bar.pack(side=tk.BOTTOM, fill=tk.X)
    
    def add_batch_files(self):
        """添加批量处理文件"""
        files = filedialog.askopenfilenames(
            title="选择要处理的文件",
            filetypes=(("文本文件", "*.txt"), ("Excel文件", "*.xlsx"), ("CSV文件", "*.csv"), ("所有文件", "*.*"))
        )
        
        if files:
            for file in files:
                if file not in self.batch_files:
                    self.batch_files.append(file)
                    self.file_listbox.insert(tk.END, os.path.basename(file))
            self.status_var_batch.set(f"添加了 {len(files)} 个文件")
    
    def remove_selected_files(self):
        """移除选中的文件"""
        selected = self.file_listbox.curselection()
        if not selected:
            return
            
        # 从后往前删除避免索引变化
        for idx in sorted(selected, reverse=True):
            del self.batch_files[idx]
            self.file_listbox.delete(idx)
        
        self.status_var_batch.set(f"移除了 {len(selected)} 个文件")
    
    def clear_file_list(self):
        """清空文件列表"""
        self.batch_files = []
        self.file_listbox.delete(0, tk.END)
        self.status_var_batch.set("文件列表已清空")
    
    def browse_output_dir(self):
        """选择输出目录"""
        directory = filedialog.askdirectory(
            title="选择输出目录",
            mustexist=False
        )
        if directory:
            self.output_dir_var.set(directory)
    
    def browse_input_file(self):
        """浏览输入文件"""
        file_path = filedialog.askopenfilename(
            title="选择输入文件",
            filetypes=(("文本文件", "*.txt"), ("Excel文件", "*.xlsx"), ("CSV文件", "*.csv"), ("所有文件", "*.*"))
        )
        if file_path:
            self.input_file_path.set(file_path)
    
    def browse_steady_input_file(self):
        """浏览稳态分析输入文件"""
        file_path = filedialog.askopenfilename(
            title="选择处理后的数据文件",
            filetypes=(("文本文件", "*.txt"), ("CSV文件", "*.csv"), ("所有文件", "*.*"))
        )
        if file_path:
            self.steady_input_path.set(file_path)
            self.status_var_steady.set(f"已选择文件: {os.path.basename(file_path)}")
    
    def use_latest_processed_file(self):
        """使用最新处理结果"""
        if self.processed_file_path and os.path.exists(self.processed_file_path):
            self.steady_input_path.set(self.processed_file_path)
            self.status_var_steady.set(f"已选择最新处理文件: {os.path.basename(self.processed_file_path)}")
        else:
            messagebox.showwarning("无处理结果", "尚未处理任何文件或处理文件已不存在")
    
    def parse_gcode_line(self, line):
        """解析G代码行"""
        tokens = line.strip().split()
        if len(tokens) < 7:
            return None
        
        # 提取前6个字段
        ap = tokens[3]
        ae = tokens[4]
        feed_rate = tokens[5]
        
        # 合并剩余的字段作为G代码内容
        gcode_content = ' '.join(tokens[6:])
        
        # 提取转速S值（保留小数部分）
        s_value = None
        s_match = re.search(r'S(\d+\.?\d*)', gcode_content)
        if s_match:
            try:
                s_value = float(s_match.group(1))
            except ValueError:
                s_value = None
        
        return ap, ae, feed_rate, gcode_content, s_value
    
    def extract_coordinates(self, gcode_content, prev_coords):
        """提取坐标值"""
        # 默认使用上一行的坐标值
        x, y, z = prev_coords
        
        # 使用正则表达式提取坐标值
        if match := re.search(r'X([-+]?\d*\.?\d+)', gcode_content):
            x = float(match.group(1))
        if match := re.search(r'Y([-+]?\d*\.?\d+)', gcode_content):
            y = float(match.group(1))
        if match := re.search(r'Z([-+]?\d*\.?\d+)', gcode_content):
            z = float(match.group(1))
        
        return x, y, z
    
    def calculate_distance(self, prev_coords, current_coords):
        """计算距离"""
        if prev_coords is None:  # 第一行没有前一行
            return 0.0
        
        dx = current_coords[0] - prev_coords[0]
        dy = current_coords[1] - prev_coords[1]
        dz = current_coords[2] - prev_coords[2]
        
        return math.sqrt(dx**2 + dy**2 + dz**2)
    
    def extract_n_value(self, gcode_content):
        """提取N值（行号标识），保留小数部分"""
        # 修改正则表达式以匹配带小数的N值
        match = re.search(r'^N\d+\.?\d*', gcode_content)
        return match.group(0) if match else "N0"
    def calculate_additional_columns(self, ap, ae, feed_rate, s, current_s, p_idle, z_impedance):
        """计算新增列：加工时间(t), dMRV, MRR, Z(s), P_pred

        学术实验版：采用论文中的行程域功率方程
            P_pred(s) = P_idle + Z(s) * MRR(s)
        其中 MRR(s) = ap * ae * (F/60)  [mm³/s]，F 为 mm/min
        """
        try:
            ap_val = float(ap)
            ae_val = float(ae)
            feed_val = float(feed_rate)
            s_val = float(s)

            # 1) 加工时间 t = s / (F/60)  [s]
            if feed_val > 0:
                t_val = s_val / (feed_val / 60.0)
            else:
                t_val = 0.0

            # 2) dMRV = ap * ae  [mm²]
            dmrv_val = ap_val * ae_val

            # 3) MRR = dMRV * F/60  [mm³/s]
            mrr_val = dmrv_val * (feed_val / 60.0)

            # 4) P_pred = P_idle + Z(s) * MRR  [W]
            z_val = float(z_impedance)
            p_power = float(p_idle) + z_val * mrr_val

            return t_val, dmrv_val, mrr_val, z_val, p_power

        except (ValueError, Exception) as e:
            print(f"计算附加列时出错: {e}")
            z_val = float(z_impedance) if z_impedance is not None else 0.0
            p_idle_val = float(p_idle) if p_idle is not None else 0.0
            return 0.0, 0.0, 0.0, z_val, p_idle_val
    
    def one_click_process(self):
        """一键处理：解析文件、生成工艺信息表和图表（不自动保存）"""
        input_file = self.input_file_path.get()
        
        if not input_file:
            messagebox.showwarning("未选择文件", "请先选择要处理的txt文件")
            return
        
        if not os.path.exists(input_file):
            messagebox.showerror("错误", f"文件不存在: {input_file}")
            return
        
        try:
            # 第一步：处理数据生成工艺信息表
            self.status_var_data.set("正在处理数据...")
            self.root.update()
            
            success = self.process_single_file(input_file, save_plots=False, do_steady_analysis=False)
            
            if not success:
                return
            
            # 第二步：生成图表（不保存）
            self.status_var_data.set("正在生成图表...")
            self.root.update()
            
            self.generate_plots(save=False)  # 不自动保存图表
            
            # 第三步：显示结果
            self.show_current_figure(0)  # 显示第一张图
            
            # 完成提示 - 提醒用户需要手动保存
            messagebox.showinfo("处理完成", 
                              f"数据处理成功！\n\n"
                              f"工艺信息表已生成，共{len(self.figures)}张图表已加载。\n\n"
                              f"⚠️ 请点击'保存所有图表'按钮保存结果。")
            
            self.status_var_data.set(f"处理完成！请点击'保存所有图表'保存结果")
            
        except Exception as e:
            messagebox.showerror("处理错误", f"处理过程中发生错误:\n{str(e)}")
            self.status_var_data.set("处理失败")

    def process_data(self):
        """处理单个文件（用户界面调用）"""
        input_file = self.input_file_path.get()
        
        if not input_file:
            messagebox.showerror("错误", "请选择输入文件路径")
            return
        
        try:
            self.process_single_file(input_file)
            
            # 显示完成消息
            self.status_var_data.set(f"处理完成! 文件已保存到: {self.processed_file_path}")
            self.progress_var.set(100)  # 设置进度为100%
            messagebox.showinfo("完成", 
                            f"数据处理完成!\n" 
                            f"输出文件: {self.processed_file_path}\n" 
                            f"使用参数: S_base={self.s_base.get()}rpm, P_idle={self.p_idle.get()}W, Z(s)={self.z_impedance.get()}")
        
        except Exception as e:
            messagebox.showerror("处理错误", f"处理过程中发生错误:\n{str(e)}")
            self.status_var_data.set("处理出错")
            self.progress_var.set(0)

    def generate_plots(self, save=False):
        """生成图表"""
        if not self.data:
            messagebox.showwarning("无数据", "请先处理数据以生成图表")
            return False
        
        try:
            # 准备数据
            s_values = [d['s'] for d in self.data]
            ap_values = [d['ap'] for d in self.data]
            ae_values = [d['ae'] for d in self.data]
            dMRV_values = [d['dMRV'] for d in self.data]
            MRR_values = [d['MRR'] for d in self.data]
            P_values = [d['P'] for d in self.data]
            n_values = [d['N_str'] for d in self.data]  # 获取N列数据
            
            # 计算累计行程
            cumulative_s = np.cumsum(s_values)
            
            # 清除之前的图表
            self.figures = []
            
            # 辅助函数：在顶部添加N轴，与行程s对应
            def add_n_axis(ax, x_values):
                twin = ax.twiny()
                twin.set_xlim(ax.get_xlim())
                max_ticks = 12
                step = max(1, len(n_values) // max_ticks)
                tick_indices = list(range(0, len(n_values), step))
                tick_positions = [x_values[i] for i in tick_indices]
                twin.set_xticks(tick_positions)
                twin.set_xticklabels([n_values[i] for i in tick_indices], rotation=45, ha='left', fontsize=8)
                twin.set_xlabel('指令行号 N')
                twin.grid(False)
                return twin

            # 1. ap-s/N 图 - 使用阶梯图显示，每行在其行程区间内保持恒定 - 白色背景
            fig1, ax1 = plt.subplots(figsize=(16, 9), dpi=100)
            fig1.patch.set_facecolor('white')
            ax1.set_facecolor('white')
            
            # 使用step函数，where='post'表示在区间内保持值不变
            ax1.step(cumulative_s, ap_values, color='black', linewidth=0.8, where='post', zorder=5)
            ax1.set_xlabel('行程 s (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax1.set_ylabel('切深 ap (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax1.tick_params(labelsize=13, colors='#333333')
            
            # 应用样式和调整范围
            ax1.set_title('切深变化', fontsize=18, fontweight='bold', color='#333333', pad=15)
            ax1.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
            x_min, x_max = ax1.get_xlim()
            y_min, y_max = ax1.get_ylim()
            x_range, y_range = x_max - x_min, y_max - y_min
            ax1.set_xlim(x_min - x_range * 0.05, x_max + x_range * 0.15)
            ax1.set_ylim(y_min - y_range * 0.05, y_max + y_range * 0.15)
            add_n_axis(ax1, cumulative_s)
            fig1.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
            self.figures.append(fig1)
            
            # 2. ae-s/N 图 - 阶梯图 - 白色背景
            fig2, ax2 = plt.subplots(figsize=(16, 9), dpi=100)
            fig2.patch.set_facecolor('white')
            ax2.set_facecolor('white')
            
            ax2.step(cumulative_s, ae_values, color='black', linewidth=0.8, where='post', zorder=5)
            ax2.set_xlabel('行程 s (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax2.set_ylabel('切宽 ae (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax2.tick_params(labelsize=13, colors='#333333')
            
            ax2.set_title('切宽变化', fontsize=18, fontweight='bold', color='#333333', pad=15)
            ax2.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
            x_min, x_max = ax2.get_xlim()
            y_min, y_max = ax2.get_ylim()
            x_range, y_range = x_max - x_min, y_max - y_min
            ax2.set_xlim(x_min - x_range * 0.05, x_max + x_range * 0.15)
            ax2.set_ylim(y_min - y_range * 0.05, y_max + y_range * 0.15)
            add_n_axis(ax2, cumulative_s)
            fig2.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
            self.figures.append(fig2)
            
            # 3. MRR-s/N 图 - 阶梯图 - 白色背景
            fig3, ax3 = plt.subplots(figsize=(16, 9), dpi=100)
            fig3.patch.set_facecolor('white')
            ax3.set_facecolor('white')
            
            ax3.step(cumulative_s, MRR_values, color='black', linewidth=0.8, where='post', zorder=5)
            ax3.set_xlabel('行程 s (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax3.set_ylabel('材料去除率 MRR (mm$^3$/s)', fontsize=14, fontweight='bold', color='#333333')
            ax3.tick_params(labelsize=13, colors='#333333')
            
            ax3.set_title('材料去除率', fontsize=18, fontweight='bold', color='#333333', pad=15)
            ax3.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
            x_min, x_max = ax3.get_xlim()
            y_min, y_max = ax3.get_ylim()
            x_range, y_range = x_max - x_min, y_max - y_min
            ax3.set_xlim(x_min - x_range * 0.05, x_max + x_range * 0.15)
            ax3.set_ylim(y_min - y_range * 0.05, y_max + y_range * 0.15)
            add_n_axis(ax3, cumulative_s)
            fig3.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
            self.figures.append(fig3)
            
            # 4. P-s/N 图 - 阶梯图 - 白色背景
            fig4, ax4 = plt.subplots(figsize=(16, 9), dpi=100)
            fig4.patch.set_facecolor('white')
            ax4.set_facecolor('white')
            
            ax4.step(cumulative_s, P_values, color='black', linewidth=0.8, where='post', zorder=5)
            ax4.set_xlabel('行程 s (mm)', fontsize=14, fontweight='bold', color='#333333')
            ax4.set_ylabel('功率 P (W)', fontsize=14, fontweight='bold', color='#333333')
            ax4.tick_params(labelsize=13, colors='#333333')
            
            ax4.set_title('主轴功率预测', fontsize=18, fontweight='bold', color='#333333', pad=15)
            ax4.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
            x_min, x_max = ax4.get_xlim()
            y_min, y_max = ax4.get_ylim()
            x_range, y_range = x_max - x_min, y_max - y_min
            ax4.set_xlim(x_min - x_range * 0.05, x_max + x_range * 0.15)
            ax4.set_ylim(y_min - y_range * 0.05, y_max + y_range * 0.15)
            add_n_axis(ax4, cumulative_s)
            fig4.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
            self.figures.append(fig4)
            
            # 5. MRR稳态区间划分图 - 如果启用
            if self.enable_mrr_steady.get():
                self.mrr_intervals = self.partition_mrr_steady_intervals(
                    MRR_values, s_values, cumulative_s, n_values
                )
                
                # 生成MRR稳态区间图 - 白色背景
                fig5, ax5 = plt.subplots(figsize=(16, 9), dpi=100)
                fig5.patch.set_facecolor('white')
                ax5.set_facecolor('white')

                # 标记稳态区间 - 显示全部区间（包括MRR为0的区间）
                cut_intervals = self.mrr_intervals  # 不再过滤，显示全部区间
                n_iv = len(cut_intervals)

                                # 显示全部区间：相邻区间交替高对比颜色（亮蓝/亮橙）
                interval_colors = ['#00A3FF', '#FF6A00']
                for idx, interval in enumerate(cut_intervals):
                    c = interval_colors[idx % 2]
                    # 关键：给极窄区间加边框线，避免“看不见”
                    ax5.axvspan(interval['start_s'], interval['end_s'],
                               alpha=0.42, facecolor=c,
                               edgecolor=c, linewidth=0.35, zorder=0)

# 绘制MRR曲线（在区间上方）- 使用黑色细线，zorder=10 确保在最上层
                ax5.step(cumulative_s, MRR_values, color='black', linewidth=0.8, 
                        where='post', label='MRR', zorder=10)
                
                ax5.set_xlabel('行程 s (mm)', fontsize=14, fontweight='bold', color='#333333')
                ax5.set_ylabel('材料去除率 MRR (mm$^3$/s)', fontsize=14, fontweight='bold', color='#333333')
                ax5.tick_params(labelsize=13, colors='#333333')
                
                # 配置图例
                legend = ax5.legend(loc='upper right', fontsize=13, framealpha=0.9, shadow=True)
                legend.get_frame().set_facecolor('white')
                legend.get_frame().set_edgecolor('#333333')
                legend.get_frame().set_linewidth(1.5)
                for text in legend.get_texts():
                    text.set_color('#333333')
                
                # 设置标题和调整布局
                ax5.set_title(f'MRR稳态区间划分 (共{len(self.mrr_intervals)}个区间)', 
                             fontsize=18, fontweight='bold', color='#333333', pad=15)
                # 关键：网格设置为zorder=-1，确保在最底层
                ax5.grid(True, alpha=0.3, linestyle='--', linewidth=0.5, zorder=-1)
                
                # 关键：强制设置Y轴范围，留出上下10%的余量，防止图形顶格
                if MRR_values:
                    mrr_min = min(MRR_values)
                    mrr_max = max(MRR_values)
                    mrr_range = mrr_max - mrr_min if mrr_max > mrr_min else 1
                    ax5.set_ylim(mrr_min - mrr_range * 0.1, mrr_max + mrr_range * 0.1)
                
                # 调整X轴范围
                x_min, x_max = ax5.get_xlim()
                x_range = x_max - x_min
                ax5.set_xlim(x_min - x_range * 0.05, x_max + x_range * 0.15)
                
                add_n_axis(ax5, cumulative_s)
                fig5.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
                self.figures.append(fig5)
            
            # 更新图表名称列表与下拉选择
            self.figure_names = ["切深变化 (ap-s)", "切宽变化 (ae-s)", "材料去除率 (MRR-s)", "主轴功率预测 (P-s)"]
            if self.enable_mrr_steady.get():
                self.figure_names.append("MRR稳态区间划分")
            self.figure_selector["values"] = self.figure_names
            if self.figure_names:
                self.figure_selector.current(0)
            
            # 如果设置了保存选项，自动保存图表
            if save:
                self.save_all_plots(silent=True)
            # 显示第一张图
            self.show_current_figure(0)
            
            total_charts = len(self.figures)
            self.status_var_data.set(f"图表已生成! 共{total_charts}张图表，点击'保存所有图表'按钮保存")
            if not save:
                messagebox.showinfo("完成", f"{total_charts}张图表已成功生成! 请点击'保存所有图表'按钮保存全部图表")
            
            return True
            
        except Exception as e:
            messagebox.showerror("图表生成错误", f"生成图表时发生错误:\n{str(e)}")
            self.status_var_data.set("图表生成失败")
            return False
    
    def show_current_figure(self, index=0):
        """显示当前图表（直接渲染原始Figure，避免复制导致的元素丢失/错位）"""
        if not self.figures or index >= len(self.figures):
            return

        self.current_figure_index = index

        # 清空预览区域（销毁旧的canvas组件）
        for widget in self.data_figure_frame.winfo_children():
            widget.destroy()

        fig = self.figures[index]
        self._current_preview_fig = fig  # 供缩放等交互使用

        # 默认取主轴（缩放时会同步作用到同一Figure的其它轴）
        self.ax_data = fig.axes[0] if getattr(fig, 'axes', None) else None

        self.canvas_data = FigureCanvasTkAgg(fig, master=self.data_figure_frame)
        canvas_widget = self.canvas_data.get_tk_widget()
        canvas_widget.grid(row=0, column=0, sticky="nsew")
        canvas_widget.configure(relief=tk.FLAT, bd=0)

        # 绑定滚轮缩放交互
        try:
            self.canvas_data.mpl_connect('scroll_event', self.on_data_scroll_zoom)
        except Exception:
            pass

        self.update_nav_buttons()

        self.canvas_data.draw_idle()
        self.root.after_idle(self.adjust_figure_sizes)

    def _on_preview_canvas_configure(self, event):
        """预览区大小变化时触发图表重排（防抖避免拖拽卡顿）"""
        try:
            if getattr(self, '_preview_resize_timer', None) is not None:
                self.root.after_cancel(self._preview_resize_timer)
            # 120ms 比较平衡：拖拽不卡、放开后也能快速跟上
            self._preview_resize_timer = self.root.after(120, self.adjust_figure_sizes)
        except Exception:
            pass

    def on_figure_selected(self, event=None):
        """下拉选择图表"""
        if not self.figure_names:
            return
        selected = self.figure_selector.current()
        if selected >= 0:
            self.show_current_figure(selected)
    
    def save_all_plots(self, silent=False):
        """保存所有图表到处理数据时创建的目录"""
        if not self.figures:
            if not silent:
                messagebox.showwarning("无图表", "没有可保存的图表，请先生成图表")
            return False
        
        if not self.processed_data_dir:
            if not silent:
                messagebox.showwarning("无目录", "尚未处理数据，无法确定保存目录")
            return False
        
        try:
            # 使用之前创建的目录
            save_dir = self.processed_data_dir
            
            # 定义图表文件名 - 修改为行程域，添加ap和ae
            filenames = [
                "ap_s",   # 切深
                "ae_s",   # 切宽
                "MRR_s",  # 材料去除率
                "P_s",     # 功率
                "MRR_steady_intervals"  # MRR稳态区间（如果启用）
            ]
            
            # 保存所有图表 - 同时保存高DPI的PNG和矢量SVG格式
            for i, fig in enumerate(self.figures):
                if i < len(filenames):  # 确保不超出文件名列表范围
                    # 保存高清PNG (用于预览)
                    png_path = os.path.join(save_dir, f"{filenames[i]}.png")
                    fig.savefig(png_path, dpi=600, bbox_inches='tight', format='png')
                    
                    # 保存SVG矢量图 (可无损缩放)
                    svg_path = os.path.join(save_dir, f"{filenames[i]}.svg")
                    fig.savefig(svg_path, bbox_inches='tight', format='svg')
            
            # 如果有MRR稳态区间，保存区间数据
            if self.mrr_intervals:
                intervals_txt_path = os.path.join(save_dir, "MRR_steady_intervals.txt")
                with open(intervals_txt_path, 'w', encoding='utf-8') as f:
                    f.write("# MRR稳态区间划分结果\n")
                    f.write(f"# 最小行程长度: {self.mrr_min_length.get()} mm\n")
                    f.write(f"# 总区间数: {len(self.mrr_intervals)}\n")
                    f.write("#" + "="*80 + "\n")
                    f.write("# 区间\t起始行号\t结束行号\t起始行程(mm)\t结束行程(mm)\t长度(mm)\tMRR(mm³/s)\n")
                    for i, interval in enumerate(self.mrr_intervals, 1):
                        f.write(f"{i}\t{interval['start_n']}\t{interval['end_n']}\t"
                               f"{interval['start_s']:.3f}\t{interval['end_s']:.3f}\t"
                               f"{interval['length']:.3f}\t{interval['mrr']:.6f}\n")
            
            if not silent:
                self.status_var_data.set(f"所有图表已保存到: {save_dir}")
                messagebox.showinfo("保存成功", f"所有图表已自动保存到:\n{save_dir}")
            
            return True
        
        except Exception as e:
            if not silent:
                messagebox.showerror("保存错误", f"保存图表时发生错误:\n{str(e)}")
            return False
    
    def show_prev_figure(self):
        """显示上一张图表"""
        if not hasattr(self, 'current_figure_index'):
            self.current_figure_index = 0
        
        if self.current_figure_index > 0:
            self.show_current_figure(self.current_figure_index - 1)
    
    def show_next_figure(self):
        """显示下一张图表"""
        if not hasattr(self, 'current_figure_index'):
            self.current_figure_index = 0
        
        if self.current_figure_index < len(self.figures) - 1:
            self.show_current_figure(self.current_figure_index + 1)
    
    def partition_mrr_steady_intervals(self, MRR_values, s_values, cumulative_s, n_values):
        """
        划分MRR稳态区间：将MRR完全恒定的连续区域划分为稳态区间
        :param MRR_values: MRR值列表
        :param s_values: 各行的行程长度列表
        :param cumulative_s: 累计行程列表
        :param n_values: 指令行号列表
        :return: 稳态区间列表
        """
        min_length = self.mrr_min_length.get()  # 最小行程长度
        intervals = []
        
        if not MRR_values or len(MRR_values) == 0:
            return intervals
        
        # 将累计行程转换为列表（如果是numpy数组）
        if isinstance(cumulative_s, np.ndarray):
            cumulative_s = cumulative_s.tolist()
        
        i = 0
        while i < len(MRR_values):
            current_mrr = MRR_values[i]
            start_idx = i
            start_s = cumulative_s[i] - s_values[i] if i > 0 else 0  # 该行起始位置
            
            # 查找MRR完全相同的连续区域 - 使用浮点数近似比较
            j = i + 1
            while j < len(MRR_values):
                # 使用浮点数近似比较，容差为 1e-5
                if abs(MRR_values[j] - current_mrr) < 1e-5:
                    j += 1
                else:
                    break
            
            end_idx = j - 1
            end_s = cumulative_s[end_idx]  # 该区域结束位置
            
            # 计算该区间的行程长度
            interval_length = end_s - start_s
            
            # 如果区间长度大于等于最小长度，则保存该区间
            if interval_length >= min_length:
                intervals.append({
                    'start_idx': start_idx,
                    'end_idx': end_idx,
                    'start_s': start_s,
                    'end_s': end_s,
                    'length': interval_length,
                    'mrr': current_mrr,
                    'start_n': n_values[start_idx],
                    'end_n': n_values[end_idx]
                })
            
            i = j
        
        return intervals
    
    def update_nav_buttons(self):
        """更新导航按钮状态"""
        if not hasattr(self, 'current_figure_index'):
            self.current_figure_index = 0
        
        if not self.figures:
            self.prev_btn.config(state=tk.DISABLED)
            self.next_btn.config(state=tk.DISABLED)
            self.figure_label.config(text="")
            self.figure_selector["values"] = []
            self.figure_selector_var.set("")
            return
        
        # 更新标签
        if self.current_figure_index < len(self.figure_names):
            self.figure_label.config(text=f"{self.current_figure_index + 1}/{len(self.figures)} - {self.figure_names[self.current_figure_index]}")
        else:
            self.figure_label.config(text=f"{self.current_figure_index + 1}/{len(self.figures)}")

        # 同步下拉选择
        if self.figure_names and self.current_figure_index < len(self.figure_names):
            self.figure_selector.current(self.current_figure_index)
        
        # 更新按钮状态
        self.prev_btn.config(state=tk.NORMAL if self.current_figure_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if self.current_figure_index < len(self.figures) - 1 else tk.DISABLED)
        
    def detect_file_encoding(self,file_path):
        """使用 Python 内置方法检测文件编码"""
        # 常见编码列表，按优先级排序
        encodings = ['utf-8', 'gbk', 'gb2312', 'latin1', 'iso-8859-1', 'cp1252']
        
        for encoding in encodings:
            try:
                with open(file_path, 'r', encoding=encoding) as f:
                    # 尝试读取文件内容
                    f.read(1024)  # 只读取前1024字节进行测试
                return encoding
            except UnicodeDecodeError:
                continue
        
        # 如果所有编码都失败，返回默认编码
        return 'utf-8'
 
    def save_steady_results(self, save_dir):
        """保存稳态分析结果到指定目录"""
        if not self.intervals:
            return False
        
        if self.cumulative_time is None:
            messagebox.showerror("错误", "稳态分析尚未完成，时间累计数据未生成。")
            return False
        
        try:
            # 创建目录（如果不存在）
            os.makedirs(save_dir, exist_ok=True)
            
            # 1. 单独保存时域稳态区间图 - 同时保存PNG和SVG
            fig_time_png = os.path.join(save_dir, "steady_state_time_domain.png")
            fig_time_svg = os.path.join(save_dir, "steady_state_time_domain.svg")
            self.fig_steady_time.savefig(fig_time_png, dpi=600, bbox_inches='tight', format='png')
            self.fig_steady_time.savefig(fig_time_svg, bbox_inches='tight', format='svg')
            
            # 2. 单独保存指令域稳态区间图 - 同时保存PNG和SVG
            fig_n_png = os.path.join(save_dir, "steady_state_n_domain.png")
            fig_n_svg = os.path.join(save_dir, "steady_state_n_domain.svg")
            self.fig_steady_n.savefig(fig_n_png, dpi=600, bbox_inches='tight', format='png')
            self.fig_steady_n.savefig(fig_n_svg, bbox_inches='tight', format='svg')
            
            # 3. 保存区间数据
            txt_path = os.path.join(save_dir, "steady_intervals.txt")
            with open(txt_path, 'w', encoding='utf-8') as f:
                f.write("# 稳态区间划分结果\n")
                f.write("# 起始索引\t结束索引\t起始程序行号.点索引\t结束程序行号.点索引\t长度(点)\n")
                for i, (start_idx, end_idx) in enumerate(self.intervals):
                    # 获取程序行号和行内索引
                    start_ln = self.steady_line_numbers[start_idx]
                    start_point_idx = self.steady_point_indices[start_idx]
                    end_ln = self.steady_line_numbers[min(end_idx, len(self.steady_line_numbers)-1)]
                    end_point_idx = self.steady_point_indices[min(end_idx, len(self.steady_point_indices)-1)]
                    
                    length_points = min(end_idx, len(self.n_values)-1) - start_idx + 1
                    
                    # 使用新格式保存区间
                    f.write(f"{start_idx}\t{end_idx}\t{start_ln:.0f}.{start_point_idx}\t{end_ln:.0f}.{end_point_idx}\t{length_points}\n")
            
            return True
        
        except Exception as e:
            return False
    
    def parse_channel_data_file(self, file_path):
        """解析包含ChannelInfo和ChannelData的文件格式"""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    
        # 使用正则表达式提取ChannelInfo块
        channel_info_blocks = re.findall(r'<ChannelInfo>\s*([^<]*)', content)
        load_current_col = None
        program_line_col = None
        for i, block in enumerate(channel_info_blocks):
            lines = block.strip().split('\n')
            lines = [line.strip() for line in lines if line.strip()]
            if len(lines) >= 3:
                name = lines[2].strip('<> ')
                if name == '负载电流':
                    load_current_col = i
                elif name == '程序行号':
                    program_line_col = i
    
        if load_current_col is None or program_line_col is None:
            raise ValueError("无法找到负载电流或程序行号通道")
    
        # 解析ChannelData块
        channel_data_blocks = re.findall(r'<ChannelData>\s*([^<]*)', content)
        currents = []
        program_lines = []
        for block in channel_data_blocks:
            lines = block.strip().split('\n')
            lines = [line.strip() for line in lines if line.strip()]
            if len(lines) > max(load_current_col, program_line_col):
                try:
                    current_val = float(lines[load_current_col])
                    program_line_val = lines[program_line_col].strip()
                    currents.append(current_val)
                    program_lines.append(program_line_val)
                except ValueError:
                    continue  # 跳过无法转换的数字
    
        return currents, program_lines
        
    def load_data(self):
        """加载数据"""
        file_path = self.steady_input_path.get()
        
        if not file_path:
            messagebox.showerror("错误", "请选择输入文件")
            return
        
        if not os.path.exists(file_path):
            messagebox.showerror("错误", f"文件不存在: {file_path}")
            return
        
        try:
            # 确定文件编码
            encoding_choice = self.encoding_var.get()
            if encoding_choice == "auto":
                encoding = self.detect_file_encoding(file_path)
            else:
                encoding = encoding_choice
            
            # 读取数据文件，忽略以#开头的行
            df = pd.read_csv(file_path, sep='\t', encoding=encoding, comment='#')
            
            # 提取功率/电流列
            if 'P(功率)' in df.columns:
                currents_col = 'P(功率)'
            elif 'I(电流)' in df.columns:
                currents_col = 'I(电流)'
            else:
                possible_cols = [col for col in df.columns if any(key in col for key in ['功率', 'P', '电流', 'I'])]
                if possible_cols:
                    currents_col = possible_cols[0]
                    self.status_var_steady.set(f"使用 '{currents_col}' 作为功率/电流列")
                else:
                    messagebox.showerror("错误", "数据文件中缺少功率/电流列 (请确认列名包含'P(功率)'或'I(电流)')")
                    return
            
            self.currents = df[currents_col].values
            
            # 提取时间列并计算累计时间
            if 't(时间)' not in df.columns:
                # 尝试匹配相似的列名
                possible_cols = [col for col in df.columns if '时间' in col or 't' in col]
                if possible_cols:
                    self.status_var_steady.set(f"使用 '{possible_cols[0]}' 作为时间列")
                    time_col = possible_cols[0]
                else:
                    messagebox.showerror("错误", "数据文件中缺少时间列 (请确认列名包含't(时间)')")
                    return
            else:
                time_col = 't(时间)'
            
            t_values = df[time_col].values
            
            # 在load_data函数中
            # 提取N列数据
            if 'N' not in df.columns:
                # 尝试匹配相似的列名
                possible_cols = [col for col in df.columns if '指令行号' in col or 'N' in col]
                if possible_cols:
                    self.status_var_actual_load.set(f"使用 '{possible_cols[0]}' 作为N列")
                    n_col = possible_cols[0]
                else:
                    messagebox.showerror("错误", "数据文件中缺少N列 (请确认列名包含'N')")
                    return
            else:
                n_col = 'N'

            # 为稳态分析存储程序行号数据
            self.n_values = df[n_col].values
            self.steady_line_numbers = df[n_col].values
            
            # 计算每个数据点在其程序行号内的点数索引
            self.steady_point_indices = []
            line_point_counts = {}  # 记录每行的数据点数量
            
            for line_number in self.steady_line_numbers:
                line_number = int(line_number)  # 确保是整数
                if line_number not in line_point_counts:
                    line_point_counts[line_number] = 1
                else:
                    line_point_counts[line_number] += 1
                self.steady_point_indices.append(line_point_counts[line_number])
            
            self.cumulative_time = np.cumsum(np.asarray(t_values))
            
            # 显示数据摘要
            self.status_var_steady.set(f"成功加载数据: {len(self.currents)}个数据点")
            self.result_text.delete(1.0, tk.END)
            self.result_text.insert(tk.END, f"数据文件: {os.path.basename(file_path)}\n")
            self.result_text.insert(tk.END, f"文件编码: {encoding}\n")
            self.result_text.insert(tk.END, f"数据点数: {len(self.currents)}\n")
            currents_array = np.asarray(self.currents)
            self.result_text.insert(tk.END, f"电流范围: {np.min(currents_array):.2f}A - {np.max(currents_array):.2f}A\n")
            self.result_text.insert(tk.END, f"时间范围: {self.cumulative_time[0]:.2f}s - {self.cumulative_time[-1]:.2f}s\n")
            
            # 绘制电流原始数据预览（添加指令域预览）
            fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
            
            # 时间域电流预览
            ax1.plot(np.asarray(self.cumulative_time), np.asarray(self.currents), 'b-', linewidth=1.0)
            ax1.set_title('时间域电流原始数据预览')
            ax1.set_xlabel('时间 (秒)')
            ax1.set_ylabel('电流 (A)')
            ax1.grid(True, linestyle='--', alpha=0.7)
            
            # 指令域电流预览
            positions = range(len(self.n_values))
            ax2.plot(positions, np.asarray(self.currents), 'g-', linewidth=1.0)
            ax2.set_title('指令域电流原始数据预览')
            ax2.set_xlabel('指令行号索引')
            ax2.set_ylabel('电流 (A)')
            
            # 设置横轴刻度标签
            if len(self.n_values) > 100:
                step = max(1, len(self.n_values) // 20)
                tick_positions = positions[::step]
                visible_labels = [self.n_values[i] for i in tick_positions]
                ax2.set_xticks(tick_positions)
                ax2.set_xticklabels(visible_labels, rotation=45, ha='right', fontsize=8)
            else:
                ax2.set_xticks(positions)
                ax2.set_xticklabels(self.n_values, rotation=45, ha='right', fontsize=8)
            
            ax2.grid(True, linestyle='--', alpha=0.7)
            
            plt.tight_layout()
            
            self.ax_steady_time.clear()
            self.ax_steady_time.text(0.5, 0.5, "数据已加载\n请点击'运行分析'按钮", 
                                    horizontalalignment='center', 
                                    verticalalignment='center',
                                    fontsize=14,
                                    color='green')
            self.ax_steady_time.axis('off')
            
            self.ax_steady_n.clear()
            self.ax_steady_n.text(0.5, 0.5, "数据已加载\n请点击'运行分析'按钮", 
                                  horizontalalignment='center', 
                                  verticalalignment='center',
                                  fontsize=14,
                                  color='green')
            self.ax_steady_n.axis('off')
            
            self.canvas_steady_time.draw()
            self.canvas_steady_n.draw()
            
            # 重置分析运行标志
            self.analysis_run = False
            
        except UnicodeDecodeError as ude:
            messagebox.showerror("编码错误", f"使用编码 '{encoding}' 读取文件失败:\n{str(ude)}\n请尝试其他编码")
            self.status_var_steady.set(f"编码错误: {encoding}")
        except Exception as e:
            messagebox.showerror("加载错误", f"加载数据时发生错误:\n{str(e)}")
            self.status_var_steady.set("加载失败")
    
    def find_steady_state_intervals(self, currents: Union[List[float], np.ndarray], 
                           min_length: int = 1, 
                           relative_threshold: float = 0.2,
                           absolute_threshold: float = 0.05,
                           adaptive: bool = True,
                           respect_user_thresholds: bool = True) -> List[Tuple[int, int]]:
        """
        从电流序列中提取稳态区间（使用自适应阈值和局部数据特性分析）
        
        参数:
            currents: 电流值列表（浮点数）
            min_length: 最小区间长度
            relative_threshold: 相对波动阈值（百分比）基准值
            absolute_threshold: 绝对阈值（窗口内所有值都必须小于此值）
            adaptive: 是否启用自适应算法
            respect_user_thresholds: 是否尊重用户设置的阈值（True时不对绝对阈值设上限）
        
        返回:
            稳态区间列表，每个区间为元组(start_index, end_index)
        """
        n = len(currents)
        if n == 0:
            return []
            
        # 数据预分析 - 计算整体统计特征
        data_array = np.asarray(currents)
        global_mean = np.mean(data_array)
        global_std = np.std(data_array)
        global_range = np.max(data_array) - np.min(data_array)
        noise_level = self.estimate_noise_level(data_array)
        

        
        # 如果启用自适应模式，基于数据特性调整阈值参数
        if adaptive:
            # 针对噪声水平较高的数据，适当放宽阈值
            if noise_level > 0.1 * global_mean:
                relative_threshold = min(0.3, relative_threshold * 1.5)
                if respect_user_thresholds:
                    # 如果尊重用户阈值，不设上限
                    absolute_threshold = absolute_threshold * 1.5
                else:
                    absolute_threshold = min(0.2, absolute_threshold * 1.5)
            
            # 针对数据范围很小的情况，减小绝对阈值
            if global_range < 0.2 * global_mean:
                if respect_user_thresholds:
                    # 如果尊重用户阈值，不能小于用户设置的原始值
                    adjusted_threshold = min(absolute_threshold, global_range * 0.3)
                    absolute_threshold = max(absolute_threshold, adjusted_threshold)
                else:
                    absolute_threshold = min(absolute_threshold, global_range * 0.3)
            
            # 针对数据范围很大的情况，使用分段相对阈值
            use_segmented_thresholds = (global_range > 0.5 * global_mean)
        else:
            use_segmented_thresholds = False
        
        left = 0
        intervals = []
        
        while left < n:
            current_sum = 0.0
            min_deque = collections.deque()
            max_deque = collections.deque()
            right = left
            
            # 直接使用用户设置的阈值，不进行任何调整
            local_relative_threshold = relative_threshold
            local_absolute_threshold = absolute_threshold
            
            if adaptive and use_segmented_thresholds:
                # 计算局部数据特性（前100个点或剩余点）
                local_window = min(100, n - left)
                if local_window > 10:  # 确保有足够的点进行分析
                    local_data = data_array[left:left+local_window]
                    local_mean = np.mean(local_data)
                    local_std = np.std(local_data)
                    local_noise = self.estimate_noise_level(local_data)
                    
                    # 根据局部特性动态调整阈值
                    # 1. 局部噪声较高时增加阈值
                    if local_noise > 0.05 * local_mean:
                        noise_factor = min(2.0, 1.0 + local_noise / local_mean)
                        local_relative_threshold *= noise_factor
                        if respect_user_thresholds:
                            # 如果尊重用户阈值，只允许增加绝对阈值，不能减小
                            local_absolute_threshold = max(absolute_threshold, local_absolute_threshold * noise_factor)
                        else:
                            local_absolute_threshold *= noise_factor
                    
                    # 2. 局部标准差较小时减小阈值
                    if local_std < 0.1 * local_mean:
                        local_relative_threshold = max(0.05, local_relative_threshold * 0.7)
                        if respect_user_thresholds:
                            # 如果尊重用户阈值，不减小绝对阈值
                            local_absolute_threshold = max(absolute_threshold, local_absolute_threshold * 0.7)
                        else:
                            local_absolute_threshold = max(0.01, local_absolute_threshold * 0.7)
                    
                    # 3. 确保阈值在合理范围内
                    local_relative_threshold = min(0.4, max(0.05, local_relative_threshold))
                    if respect_user_thresholds:
                        # 如果尊重用户阈值，确保不小于用户设置的原始值
                        local_absolute_threshold = max(absolute_threshold, local_absolute_threshold)
                    else:
                        # 原来的限制逻辑
                        local_absolute_threshold = min(0.5, max(0.01, local_absolute_threshold))
                    

            
            # 扩展右指针直到窗口不满足条件
            while right < n:
                c = currents[right]
                current_sum += c
                
                # 维护最小值双端队列（单调递增）
                while min_deque and min_deque[-1] > c:
                    min_deque.pop()
                min_deque.append(c)
                
                # 维护最大值双端队列（单调递减）
                while max_deque and max_deque[-1] < c:
                    max_deque.pop()
                max_deque.append(c)
                
                length = right - left + 1
                mean = current_sum / length
                
                # 检查波动条件 - 使用自适应阈值
                min_val = min_deque[0]
                max_val = max_deque[0]
                range_val = max_val - min_val
                
                # 严格使用用户设置的阈值，不进行任何调整
                temp_rel_threshold = local_relative_threshold
                temp_abs_threshold = local_absolute_threshold
                
                # 旧的自适应长度调整（已禁用）
                # if adaptive and length > min_length * 2:
                #     length_factor = min(1.5, 1.0 + (length - min_length) / (10 * min_length))
                #     temp_rel_threshold = local_relative_threshold * length_factor
                #     temp_abs_threshold = local_absolute_threshold * length_factor
                
                # 条件1: 相对波动不超过阈值
                condition1 = (min_val >= (1 - temp_rel_threshold) * mean and 
                            max_val <= (1 + temp_rel_threshold) * mean)
                
                # 条件2: 绝对波动不超过阈值
                condition2 = (max_val <= temp_abs_threshold)
                
                # 满足任一条件即可
                if condition1 or condition2:
                    right += 1  # 满足条件继续扩展
                else:
                    break  # 不满足条件时跳出
            
            # 记录有效区间（[left, right-1]）
            if right - left >= min_length:
                intervals.append((left, right - 1))
            
            # 移动左指针到第一个不满足点的位置
            left = right
        
        # 后处理 - 合并接近的区间
        if adaptive and intervals:
            # 区间合并处理 - 根据数据特性调整合并距离
            merge_distance = max(1, int(min_length * 0.2))  # 默认合并距离
            
            # 如果噪声水平高，适当增加合并距离
            if noise_level > 0.05 * global_mean:
                merge_distance = max(2, int(min_length * 0.3))
                
            intervals = self.merge_close_intervals(intervals, merge_distance)
        
        # 处理区间重叠
        intervals = self.adjust_overlapping_intervals(intervals, overlap_tolerance=10)
        return intervals
        
    def estimate_noise_level(self, data):
        """估计数据的噪声水平，使用相邻点差值的标准差"""
        if len(data) < 3:
            return 0
        
        # 计算相邻点差值
        diffs = np.abs(np.diff(data))
        
        # 使用相邻差值的标准差作为噪声估计
        return np.std(diffs)
        
    def merge_close_intervals(self, intervals, max_gap):
        """合并间隔小于或等于max_gap的相邻区间"""
        if not intervals or len(intervals) < 2:
            return intervals
            
        # 按起始位置排序
        intervals.sort(key=lambda x: x[0])
        
        merged = []
        current_start, current_end = intervals[0]
        
        for next_start, next_end in intervals[1:]:
            if next_start - current_end <= max_gap + 1:
                # 合并区间
                current_end = max(current_end, next_end)
            else:
                # 保存当前区间，开始新区间
                merged.append((current_start, current_end))
                current_start, current_end = next_start, next_end
                
        # 添加最后一个区间
        merged.append((current_start, current_end))
        
        return merged

    def adjust_overlapping_intervals(self, intervals, overlap_tolerance=10):
        """
        调整重叠的区间边界，消除重叠
        前一个区间终点前移overlap_tolerance点，后一个区间起点后移overlap_tolerance点
        """
        if not intervals or len(intervals) < 2:
            return intervals
        
        adjusted = []
        adjusted.append(intervals[0])
        
        for i in range(1, len(intervals)):
            prev_start, prev_end = adjusted[-1]
            curr_start, curr_end = intervals[i]
            
            # 检查是否存在重叠
            if prev_end >= curr_start:
                # 计算重叠长度
                overlap_length = prev_end - curr_start + 1
                
                # 调整前一个区间的终点
                adjust_amount = min(overlap_tolerance, overlap_length)
                new_prev_end = max(prev_start, prev_end - adjust_amount)
                
                # 调整当前区间的起点
                new_curr_start = min(curr_end, curr_start + adjust_amount)
                
                # 确保调整后的区间仍然有效
                if new_prev_end >= prev_start and new_curr_start <= curr_end:
                    adjusted[-1] = (prev_start, new_prev_end)
                    adjusted.append((new_curr_start, curr_end))
                else:
                    # 如果调整无效，保持原区间
                    adjusted.append((curr_start, curr_end))
            else:
                adjusted.append((curr_start, curr_end))
        
        return adjusted

    def convert_n_interval(self, start_n, end_n):
        """将行号区间转换为整数形式 [N34.18, N40.2] -> [N35, N39]"""
        try:
            # 提取数字部分并转换为浮点数
            start_num = float(start_n[1:])
            end_num = float(end_n[1:])
            
            # 起始行号向上取整，结束行号向下取整后减1
            start_int = int(math.ceil(start_num))
            end_int = int(math.floor(end_num)) - 1
            
            return f"N{start_int}", f"N{end_int}"
        except:
            # 如果转换失败，返回原始值
            return start_n, end_n
    
    def analyze_data(self):
        """分析数据"""
        if self.currents is None or self.cumulative_time is None or self.n_values is None:
            messagebox.showwarning("无数据", "请先加载完整数据文件")
            return
        
        try:
            min_len = self.min_length.get()
            if min_len < 1:
                messagebox.showwarning("参数错误", "最小区间长度必须大于0")
                return
            
            # 获取波动阈值
            threshold = self.steady_threshold.get()
            absolute_threshold = self.absolute_threshold.get()  # 获取绝对阈值
            
            # 应用稳态区间划分算法 - 修改为按照程序行号顺序
            # 首先按照程序行号对数据进行排序
            n_array = np.asarray(self.n_values)
            sorted_indices = np.argsort(n_array)
            sorted_currents = np.asarray(self.currents)[sorted_indices]
            sorted_line_numbers = n_array[sorted_indices]

            # 在排序后的数据上应用稳态区间划分
            raw_intervals = self.find_steady_state_intervals(
                sorted_currents, 
                min_len, 
                threshold,
                absolute_threshold,  # 传递绝对阈值
                adaptive=False,  # 禁用自适应，严格按照用户设置的阈值
                respect_user_thresholds=True  # 尊重用户设置的阈值
            )
            # 新增：再次检查并处理区间重叠（确保双重保护）
            raw_intervals = self.adjust_overlapping_intervals(raw_intervals, overlap_tolerance=10)
            # 将区间索引转换回原始数据索引
            original_intervals = []
            for start_idx, end_idx in raw_intervals:
                original_start = sorted_indices[start_idx]
                original_end = sorted_indices[end_idx]
                original_intervals.append((original_start, original_end))

            # 确保区间按照程序行号顺序排列
            original_intervals.sort(key=lambda x: self.n_values[x[0]].item())

            if not original_intervals:
                messagebox.showinfo("结果", "未找到稳态区间")
                self.status_var_steady.set("未找到稳态区间")
                return

            # 根据复选框决定是否缩减区间
            reduce_interval = self.reduce_interval_steady.get()
            self.intervals = []
            for (start_idx, end_idx) in original_intervals:
                if reduce_interval and end_idx - start_idx >= 2:
                    adjusted_start = start_idx + 1
                    adjusted_end = end_idx - 1
                    self.intervals.append((adjusted_start, adjusted_end))
                else:
                    self.intervals.append((start_idx, end_idx))

            # 更新结果文本
            self.result_text.delete(1.0, tk.END)
            self.result_text.insert(tk.END, f"找到 {len(self.intervals)} 个稳态区间:\n\n")
            self.result_text.insert(tk.END, "索引区间\t时间区间\t\t指令行号区间\t\t长度(点)\t时长(秒)\n")
            self.result_text.insert(tk.END, "-" * 80 + "\n")
            
            # 计算每个区间的平均电流
            self.interval_currents = []
            
            for i, (start_idx, end_idx) in enumerate(self.intervals):
                start_time = self.cumulative_time[start_idx]
                end_time = self.cumulative_time[min(end_idx, len(self.cumulative_time)-1)]
                length_points = min(end_idx, len(self.n_values)-1) - start_idx + 1
                duration = end_time - start_time
                
                # 获取原始行号
                start_n_raw = self.n_values[start_idx]
                end_n_raw = self.n_values[min(end_idx, len(self.n_values)-1)]
                
                # 转换为整数行号区间
                start_n_int, end_n_int = self.convert_n_interval(start_n_raw, end_n_raw)
                
                # 在结果文本中使用处理后的整数行号
                self.result_text.insert(tk.END, 
                                    f"[{start_idx}, {end_idx}]\t" +
                                    f"[{start_time:.2f}s, {end_time:.2f}s]\t" +
                                    f"[{start_n_int}, {end_n_int}]\t" +  # 使用处理后的行号
                                    f"{length_points}\t\t{duration:.2f}s\n")
            
            # 清理预览图并替换为稳态区间图
            self.ax_steady_time.clear()
            ax1 = self.ax_steady_time
            ax1.plot(np.asarray(self.cumulative_time), np.asarray(self.currents), 'b-', linewidth=1.0, label='电流值')
            interval_colors = ['#2ecc71', '#f39c12', '#3498db', '#9b59b6', '#e74c3c']
            for idx, (start_idx, end_idx) in enumerate(self.intervals):
                start_time = self.cumulative_time[start_idx]
                end_time = self.cumulative_time[end_idx]
                color = interval_colors[idx % len(interval_colors)]
                ax1.axvspan(start_time, end_time, alpha=0.35, color=color, # type: ignore
                           edgecolor=color, linewidth=0.8)
            ax1.set_title('时间域稳态区间')
            ax1.set_xlabel('时间 (秒)')
            ax1.set_ylabel('电流 (A)')
            self.cap_y_axis(ax1, [self.currents])
            ax1.grid(True, linestyle='--', alpha=0.7)
            ax1.legend(loc='upper right')
            
            # 指令域图表
            self.ax_steady_n.clear()
            ax2 = self.ax_steady_n
            positions = range(len(self.n_values))
            ax2.plot(positions, np.asarray(self.currents), 'g-', linewidth=1.0, label='电流值')
            for idx, (start_idx, end_idx) in enumerate(self.intervals):
                end_idx = min(end_idx, len(self.n_values)-1)
                color = interval_colors[idx % len(interval_colors)]
                ax2.axvspan(start_idx, end_idx, alpha=0.35, color=color, 
                           edgecolor=color, linewidth=0.8)
            ax2.set_title('指令域稳态区间')
            ax2.set_xlabel('指令行号索引')
            ax2.set_ylabel('电流 (A)')
            self.cap_y_axis(ax2, [self.currents])
            if len(self.n_values) > 100:
                step = max(1, len(self.n_values) // 20)
                tick_positions = positions[::step]
                visible_labels = [self.n_values[min(i, len(self.n_values)-1)] for i in tick_positions]
                ax2.set_xticks(tick_positions)
                ax2.set_xticklabels(visible_labels, rotation=45, ha='right', fontsize=8)
            else:
                ax2.set_xticks(positions)
                visible_labels = [self.n_values[min(i, len(self.n_values)-1)] for i in positions]
                ax2.set_xticklabels(visible_labels, rotation=45, ha='right', fontsize=8)
            ax2.grid(True, linestyle='--', alpha=0.7)
            ax2.legend(loc='upper right')
            
            # 重绘画布
            self.canvas_steady_time.draw()
            self.canvas_steady_n.draw()
            
            # 设置图表交互功能（稳态区间部分）
            self.setup_steady_chart_interactions()
            
            # 设置分析运行标志
            self.analysis_run = True
            
            # 更新状态
            reduce_status = "启用" if reduce_interval else "禁用"
            self.status_var_steady.set(f"分析完成! 找到 {len(self.intervals)} 个稳态区间 (区间缩减: {reduce_status})")
            
        except Exception as e:
            messagebox.showerror("分析错误", f"分析过程中发生错误:\n{str(e)}")
            self.status_var_steady.set("分析失败")

    def save_results(self):
        """保存结果"""
        if not self.intervals:
            messagebox.showwarning("无结果", "请先运行分析")
            return
        
        # 选择保存目录
        save_dir = filedialog.askdirectory(
            title="选择结果保存目录",
            mustexist=False
        )
        
        if not save_dir:
            return  # 用户取消选择
        
        try:
            # 创建目录（如果不存在）
            os.makedirs(save_dir, exist_ok=True)
            
            # 1. 单独保存时域稳态区间图 - 同时保存PNG和SVG
            fig_time_png = os.path.join(save_dir, "steady_state_time_domain.png")
            fig_time_svg = os.path.join(save_dir, "steady_state_time_domain.svg")
            self.fig_steady_time.savefig(fig_time_png, dpi=600, bbox_inches='tight', format='png')
            self.fig_steady_time.savefig(fig_time_svg, bbox_inches='tight', format='svg')
            
            # 2. 单独保存指令域稳态区间图 - 同时保存PNG和SVG
            fig_n_png = os.path.join(save_dir, "steady_state_n_domain.png")
            fig_n_svg = os.path.join(save_dir, "steady_state_n_domain.svg")
            self.fig_steady_n.savefig(fig_n_png, dpi=600, bbox_inches='tight', format='png')
            self.fig_steady_n.savefig(fig_n_svg, bbox_inches='tight', format='svg')
            
            # 3. 保存区间数据
            txt_path = os.path.join(save_dir, "steady_intervals.txt")
            with open(txt_path, 'w', encoding='utf-8') as f:
                f.write("# 稳态区间划分结果\n")
                f.write("# 起始索引\t结束索引\t起始程序行号.点索引\t结束程序行号.点索引\t长度(点)\n")
                for i, (start_idx, end_idx) in enumerate(self.intervals):
                    # 获取程序行号和行内索引
                    start_ln = self.steady_line_numbers[start_idx]
                    start_point_idx = self.steady_point_indices[start_idx]
                    end_ln = self.steady_line_numbers[min(end_idx, len(self.steady_line_numbers)-1)]
                    end_point_idx = self.steady_point_indices[min(end_idx, len(self.steady_point_indices)-1)]
                    
                    length_points = min(end_idx, len(self.n_values)-1) - start_idx + 1
                    
                    # 使用新格式保存区间
                    f.write(f"{start_idx}\t{end_idx}\t{start_ln:.0f}.{start_point_idx}\t{end_ln:.0f}.{end_point_idx}\t{length_points}\n")
            
            self.status_var_steady.set(f"结果已保存到: {save_dir}")
            messagebox.showinfo("保存成功", 
                              f"分析结果已保存到:\n{save_dir}\n\n" +
                              f"• 时域稳态区间图: {os.path.basename(fig_time_path)}\n" +
                              f"• 指令域稳态区间图: {os.path.basename(fig_n_path)}\n" +
                              f"• 区间数据文件: {os.path.basename(txt_path)}")
            
        except Exception as e:
            messagebox.showerror("保存错误", f"保存结果时发生错误:\n{str(e)}")
                  
    def process_single_file(self, input_file, save_plots=False, do_steady_analysis=False, base_save_dir=None, min_length=None):
        """处理单个文件的核心逻辑"""
        try:
            # 确定保存目录
            if base_save_dir:
                save_dir = os.path.join(base_save_dir, "processed_" + os.path.splitext(os.path.basename(input_file))[0])
            else:
                save_dir = os.path.join(os.path.dirname(input_file), "processed_" + os.path.splitext(os.path.basename(input_file))[0])
            
            self.processed_data_dir = save_dir
            os.makedirs(save_dir, exist_ok=True)
            
            output_filename = f"processed_{os.path.basename(input_file)}"
            output_file = os.path.join(save_dir, output_filename)
            self.processed_file_path = output_file
            
            if base_save_dir:
                origin = (
                    self.batch_origin_x.get(),
                    self.batch_origin_y.get(),
                    self.batch_origin_z.get()
                )
                rapid_speed_xy = self.batch_rapid_speed_xy.get()
                rapid_speed_z = self.batch_rapid_speed_z.get()
            else:
                origin = (
                    self.origin_x.get(),
                    self.origin_y.get(),
                    self.origin_z.get()
                )
                rapid_speed_xy = self.rapid_speed_xy.get()
                rapid_speed_z = self.rapid_speed_z.get()
            
            if base_save_dir:  # 批量处理
                tool_diameter = self.batch_tool_diameter.get()
                workpiece_material = self.batch_workpiece_material.get()
                blank_material = self.batch_blank_material.get()
            else:  # 单个文件处理
                tool_diameter = self.tool_diameter.get()
                workpiece_material = self.workpiece_material.get()
                blank_material = self.blank_material.get()
            
            # 直接打开文件处理（移除行数统计）
            with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
                # 添加材料信息作为表头注释
                outfile.write(f"# 刀具直径(mm): {tool_diameter}\n")
                outfile.write(f"# 刀具材料: {workpiece_material}\n")
                outfile.write(f"# 毛坯材料: {blank_material}\n")
                header = "ap\t\t ae\t\t F\t\t N\t\t X\t\t Y\t\t Z\t\t s(行程)\t\t t(时间)\t\t dMRV\t\t MRR\t\t S(转速)\t\t K(扭矩系数)\t\t T(扭矩)\t\t P(功率)"
                outfile.write(header + "\n")
                
                prev_coords = origin
                current_coords = origin
                data = []
                s_base = self.s_base.get()
                p_idle = self.p_idle.get()
                z_impedance = self.z_impedance.get()
                current_s = s_base
                current_feed = 0.0
                current_move_type = "rapid"  # 从机床原点开始，初始为快速移动
                
                for line_num, line in enumerate(infile):
                    parsed = self.parse_gcode_line(line)
                    if not parsed:
                        continue
                        
                    ap, ae, feed_rate, gcode_content, s_value = parsed
                    
                    # 更新转速
                    if s_value is not None:
                        current_s = s_value
                    
                    # 更新进给速度
                    if feed_rate and float(feed_rate) > 0:
                        current_feed = float(feed_rate)
                    
                    n_value = self.extract_n_value(gcode_content)
                    
                    # 提取当前坐标
                    current_coords = self.extract_coordinates(gcode_content, prev_coords)
                    
                    # 计算行程距离
                    s = self.calculate_distance(prev_coords, current_coords)
                    
                    # 确定移动类型
                    if "G0" in gcode_content or "G00" in gcode_content:
                        current_move_type = "rapid"
                    elif any(gcode in gcode_content for gcode in ["G1", "G01", "G2", "G02", "G3", "G03"]):
                        current_move_type = "cutting"
                    
                    # 根据移动类型计算时间
                    if current_move_type == "rapid":
                        dx = current_coords[0] - prev_coords[0]
                        dy = current_coords[1] - prev_coords[1]
                        dz = current_coords[2] - prev_coords[2]
                        
                        dist_xy = math.sqrt(dx**2 + dy**2)
                        dist_z = abs(dz)
                        
                        if dist_xy > 0 and dist_z == 0:
                            t_val = dist_xy / (rapid_speed_xy / 60.0)
                        elif dist_xy == 0 and dist_z > 0:
                            t_val = dist_z / (rapid_speed_z / 60.0)
                        elif dist_xy > 0 and dist_z > 0:
                            t_val_xy = dist_xy / (rapid_speed_xy / 60.0)
                            t_val_z = dist_z / (rapid_speed_z / 60.0)
                            t_val = max(t_val_xy, t_val_z)
                        else:
                            t_val = 0.0
                    else:
                        t_val = s / (current_feed / 60.0) if current_feed > 0 and s > 0 else 0.0
                    
                    # 计算工艺参数（仅切削移动）
                    if current_move_type == "cutting":
                        t_val, dmrv_val, mrr_val, z_val, p_power = self.calculate_additional_columns(
                            ap, ae, current_feed, s, current_s, p_idle, z_impedance
                        )
                    else:
                        dmrv_val = 0.0
                        mrr_val = 0.0
                        z_val = z_impedance
                        p_power = p_idle
                    
                    # 学术版：K(扭矩系数)和T(扭矩)设为占位值，因为采用Z(s)阻抗系数模型
                    k_val = 0.0
                    t_torque = 0.0
                    
                    # 写入处理后的数据
                    line_data = (
                        f"{ap}\t\t{ae}\t\t{current_feed:.1f}\t\t{n_value}\t\t"
                        f"{current_coords[0]:.4f}\t\t{current_coords[1]:.4f}\t\t{current_coords[2]:.4f}\t\t"
                        f"{s:.6f}\t\t{t_val:.6f}\t\t{dmrv_val:.6f}\t\t{mrr_val:.6f}\t\t"
                        f"{current_s:.1f}\t\t{k_val:.6f}\t\t{t_torque:.6f}\t\t{p_power:.6f}"
                    )
                    outfile.write(line_data + "\n")
                    
                    data.append({
                        's': s,
                        't': t_val,
                        'ap': float(ap),
                        'ae': float(ae),
                        'dMRV': dmrv_val,
                        'MRR': mrr_val,
                        'S': current_s,
                        'Z': z_val,
                        'P': p_power,
                        'type': current_move_type,
                        'N_str': n_value  # 存储N列字符串值
                    })
                    
                    # 更新上一行坐标
                    prev_coords = current_coords
                
                self.data = data
                
            if save_plots:
                self.generate_plots(save=True)
            
            if do_steady_analysis:
                self.steady_input_path.set(output_file)
                self.load_data()
                self.min_length.set(min_length or self.min_length.get())
                self.analyze_data()
                self.save_steady_results(save_dir)
            
            return True
        
        except Exception as e:
            raise Exception(f"处理文件 {input_file} 时出错: {str(e)}")
        
    def batch_process_files(self):
        """批量处理多个文件 - 优化版本"""
        if not self.batch_files:
            messagebox.showwarning("无文件", "请先添加要处理的文件")
            return
        
        min_length = self.min_length.get()
        if min_length < 1:
            messagebox.showwarning("参数错误", "最小区间长度必须大于0")
            return
        
        output_dir = self.output_dir_var.get()
        if not output_dir:
            first_file = self.batch_files[0]
            output_dir = os.path.dirname(first_file)
            self.output_dir_var.set(output_dir)
        
        total_files = len(self.batch_files)
        
        try:
            self.batch_progress_var.set(0)
            self.status_var_batch.set(f"开始批量处理 {total_files} 个文件...")
            
            # 禁用UI更新以提高性能
            self.root.config(cursor="watch")
            self.root.update()
            
            for idx, input_file in enumerate(self.batch_files):
                # 更新进度
                progress = (idx + 1) / total_files * 100
                self.batch_progress_var.set(progress)
                self.status_var_batch.set(f"处理文件 {idx+1}/{total_files}: {os.path.basename(input_file)}")
                
                # 强制更新UI
                self.root.update_idletasks()
                
                try:
                    # 处理当前文件
                    self.process_single_file(
                        input_file, 
                        save_plots=True, 
                        do_steady_analysis=True,
                        base_save_dir=output_dir,
                        min_length=min_length
                    )
                except Exception as e:
                    # 记录错误但继续处理其他文件
                    error_msg = f"文件 {os.path.basename(input_file)} 处理失败: {str(e)}"
                    self.status_var_batch.set(error_msg)
                    with open(os.path.join(output_dir, "batch_errors.log"), "a") as log:
                        log.write(f"{datetime.now()}: {error_msg}\n")
                
                # 清理内存 - 关键优化点
                self.data = []  # 清空数据缓存
                self.figures = []  # 释放图表内存
                plt.close('all')  # 关闭所有matplotlib图形
                
                # 强制垃圾回收
                gc.collect()
            # 恢复UI状态
            self.root.config(cursor="")
            self.batch_progress_var.set(100)
            self.status_var_batch.set(f"批量处理完成! 共处理 {total_files} 个文件")
            
            # 显示完成消息
            messagebox.showinfo("批量处理完成", 
                             f"成功处理 {total_files} 个文件!\n" 
                             f"结果已保存到: {output_dir}\n" 
                             f"错误日志: {os.path.join(output_dir, 'batch_errors.log')}")
        
        except Exception as e:
            self.root.config(cursor="")
            messagebox.showerror("批量处理错误", f"批量处理过程中发生错误:\n{str(e)}")
            self.status_var_batch.set("批量处理失败")

    def toggle_segment_mode(self):
        """切换区间分割模式"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            self.segment_mode.set(False)
            return
        
        if self.segment_mode.get():
            # 启用分割模式，连接点击事件
            self.click_cid = self.canvas_actual_load.mpl_connect('button_press_event', self.on_click_segment)
            self.status_var_actual_load.set("分割模式已启用，在图上点击设置分割点")
        else:
            # 禁用分割模式，断开点击事件
            if self.click_cid:
                self.canvas_actual_load.mpl_disconnect(self.click_cid)
                self.click_cid = None
            self.status_var_actual_load.set("分割模式已禁用")
    
    def on_click_segment(self, event):
        """处理图表点击事件，询问是否添加分割点"""
        if event.inaxes != self.ax_actual_load:
            return
        
        # 获取点击的x坐标
        x_pos = event.xdata
        if x_pos is None:
            return
        
        # 弹出确认对话框
        result = messagebox.askyesno(
            "确认添加分割点", 
            f"是否在位置 {x_pos:.2f} 处添加分割点？\n当前已有 {len(self.segment_points)} 个分割点。",
            icon='question'
        )
        
        if not result:
            return
        
        # 添加分割点
        self.segment_points.append(x_pos)
        self.segment_points.sort()  # 保持分割点有序
        
        # 绘制分割线
        line = self.ax_actual_load.axvline(x=x_pos, color='black', linestyle='--', linewidth=2, alpha=0.7)
        self.segment_lines.append(line)
        
        # 添加标签
        y_min, y_max = self.ax_actual_load.get_ylim()
        text_obj = self.ax_actual_load.text(x_pos, y_max * 0.9, f'分割点{len(self.segment_points)}', 
                                           rotation=90, ha='right', va='top', color='black', fontweight='bold')
        self.segment_texts.append(text_obj)
        
        self.canvas_actual_load.draw()
        self.status_var_actual_load.set(f"已添加分割点 {len(self.segment_points)} 个")
    
    def selective_delete_segment_points(self):
        """选择性删除分割点"""
        if not self.segment_points:
            messagebox.showinfo("无分割点", "当前没有分割点可删除")
            return
        
        # 创建删除选择窗口
        delete_window = tk.Toplevel(self.root)
        delete_window.title("选择删除分割点")
        delete_window.geometry("400x300")
        delete_window.transient(self.root)
        delete_window.grab_set()
        
        # 创建标签
        ttk.Label(delete_window, text="请选择要删除的分割点：", font=("Arial", 12)).pack(pady=10)
        
        # 创建列表框
        listbox_frame = ttk.Frame(delete_window)
        listbox_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        listbox = tk.Listbox(listbox_frame, selectmode=tk.MULTIPLE)
        scrollbar = ttk.Scrollbar(listbox_frame, orient=tk.VERTICAL)
        
        listbox.config(yscrollcommand=scrollbar.set)
        scrollbar.config(command=listbox.yview)
        
        # 填充分割点信息
        for i, point in enumerate(self.segment_points):
            listbox.insert(tk.END, f"分割点{i+1}: 位置 {point:.2f}")
        
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 按钮框架
        button_frame = ttk.Frame(delete_window)
        button_frame.pack(fill=tk.X, padx=20, pady=10)
        
        def delete_selected():
            """删除选中的分割点"""
            selected_indices = listbox.curselection()
            if not selected_indices:
                messagebox.showwarning("未选择", "请选择要删除的分割点")
                return
            
            # 按倒序删除，避免索引变化问题
            for index in sorted(selected_indices, reverse=True):
                # 删除对应的分割线和文字
                if index < len(self.segment_lines):
                    self.segment_lines[index].remove()
                    self.segment_lines.pop(index)
                
                if index < len(self.segment_texts):
                    self.segment_texts[index].remove()
                    self.segment_texts.pop(index)
                
                # 删除分割点
                if index < len(self.segment_points):
                    self.segment_points.pop(index)
            
            # 重新编号剩余的文字标签
            for i, text_obj in enumerate(self.segment_texts):
                text_obj.set_text(f'分割点{i+1}')
            
            # 清除分段数据（因为分割点改变了）
            self.segments.clear()
            self.segment_params.clear()
            
            # 清空分段选择下拉框
            if hasattr(self, 'segment_combobox'):
                self.segment_combobox['values'] = []
                self.segment_combobox.set('')
            
            # 重新绘制图表
            self.canvas_actual_load.draw()
            
            # 更新状态
            self.status_var_actual_load.set(f"已删除 {len(selected_indices)} 个分割点，剩余 {len(self.segment_points)} 个")
            
            # 关闭窗口
            delete_window.destroy()
        
        def select_all():
            """全选"""
            listbox.select_set(0, tk.END)
        
        def clear_selection():
            """清除选择"""
            listbox.selection_clear(0, tk.END)
        
        # 添加按钮
        ttk.Button(button_frame, text="全选", command=select_all).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="清除选择", command=clear_selection).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="删除选中", command=delete_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="取消", command=delete_window.destroy).pack(side=tk.LEFT, padx=5)
    
    def clear_segment_points(self):
        """清除所有分割点"""
        # 移除分割线
        for line in self.segment_lines:
            line.remove()
        
        # 移除分割点文字
        for text in self.segment_texts:
            text.remove()
        
        # 清空列表
        self.segment_points.clear()
        self.segment_lines.clear()
        self.segment_texts.clear()
        self.segments.clear()
        self.segment_params.clear()
        
        # 清空分段选择下拉框
        if hasattr(self, 'segment_combobox'):
            self.segment_combobox['values'] = []
            self.segment_combobox.set('')
        
        # 重新绘制图表
        if hasattr(self, 'canvas_actual_load'):
            self.canvas_actual_load.draw()
        
        self.status_var_actual_load.set("已清除所有分割点")
    
    def analyze_segments(self):
        """创建分段并更新界面"""
        if not hasattr(self, 'actual_load_data') or not self.actual_load_data:
            messagebox.showwarning("无数据", "请先加载数据文件")
            return
        
        if not self.segment_points:
            messagebox.showwarning("无分割点", "请先设置分割点")
            return
        
        try:
            # 确定使用哪种数据
            if self.is_filtered and self.filtered_data is not None:
                analysis_data = self.filtered_data
                data_type = "滤波"
            else:
                analysis_data = self.actual_load_data
                data_type = "原始"
            
            # 创建分段
            segments = []
            x_positions = self.actual_load_x_positions
            
            # 将分割点的x坐标转换为对应的数组索引
            segment_indices = []
            for x_coord in self.segment_points:
                # 找到最接近的x坐标对应的索引
                closest_idx = np.argmin(np.abs(np.array(x_positions) - x_coord))
                segment_indices.append(closest_idx)
            
            # 添加起始点和结束点（使用索引）
            all_points = [0] + segment_indices + [len(x_positions)]
            
            for i in range(len(all_points) - 1):
                start_idx = int(all_points[i])
                end_idx = int(all_points[i + 1])
                
                if start_idx < end_idx and end_idx <= len(analysis_data):
                    segment_data = analysis_data[start_idx:end_idx]
                    segment_x = x_positions[start_idx:end_idx]
                    
                    segments.append({
                        'index': i + 1,
                        'start_idx': start_idx,
                        'end_idx': end_idx,
                        'data': segment_data,
                        'x_positions': segment_x,
                        'intervals': []
                    })
            
            # 保存分段数据
            self.segments = segments
            
            # 初始化分段参数 - 确保使用正确的变量名
            self.segment_params = {}
            for i in range(len(segments)):
                self.segment_params[i] = {
                    'min_length': self.actual_load_min_length.get(),  # 修正：使用正确的变量名
                    'threshold': self.actual_current_threshold.get(),
                    'abs_threshold': self.absolute_threshold.get(),
                    'reduce_interval': self.reduce_interval_actual_load.get()
                }
            
            # 更新分段选择下拉框
            self.update_segment_combobox()
            
            # 刷新分段结果表格
            if hasattr(self, 'segment_results_tree'):
                self.refresh_segment_results()
            
            # 更新状态
            self.status_var_actual_load.set(f"已创建 {len(segments)} 个分段，可在分段选择区域进行单独分析或一起合并分析")
            
        except Exception as e:
            messagebox.showerror("分析错误", f"分段分析时发生错误:\n{str(e)}")
    
    def on_segment_selected(self, event=None):
        """当选择不同分段时，更新参数显示"""
        if not hasattr(self, 'segments') or not self.segments:
            return
        
        try:
            # 从"分段1"格式的字符串中提取数字
            segment_text = self.segment_combobox.get()
            if segment_text.startswith('分段'):
                segment_index = int(segment_text.replace('分段', '')) - 1  # 转换为0基索引
            else:
                segment_index = int(segment_text)
            
            # 保存当前参数到之前选择的分段
            if hasattr(self, 'prev_segment_index') and self.prev_segment_index is not None:
                self.save_current_segment_params(self.prev_segment_index)
            
            # 加载选中分段的参数
            if segment_index in self.segment_params:
                params = self.segment_params[segment_index]
                self.segment_min_length.set(params.get('min_length', 100))
                self.segment_threshold.set(params.get('threshold', 0.2))
                self.segment_abs_threshold.set(params.get('abs_threshold', 0.05))
                self.segment_reduce_interval.set(params.get('reduce_interval', True))
            else:
                # 使用默认参数 - 修正：使用正确的变量名
                self.segment_min_length.set(self.actual_load_min_length.get())
                self.segment_threshold.set(self.actual_current_threshold.get())
                self.segment_abs_threshold.set(self.absolute_threshold.get())
                self.segment_reduce_interval.set(self.reduce_interval_actual_load.get())
            
            self.prev_segment_index = segment_index
            
        except (ValueError, AttributeError):
            pass
    
    def save_current_segment_params(self, segment_index):
        """保存当前参数到指定分段"""
        self.segment_params[segment_index] = {
            'min_length': self.segment_min_length.get(),
            'threshold': self.segment_threshold.get(),
            'abs_threshold': self.segment_abs_threshold.get(),
            'reduce_interval': self.segment_reduce_interval.get()
        }
    
    def analyze_single_segment(self):
        """分析单个选中的分段"""
        if not hasattr(self, 'segments') or not self.segments:
            messagebox.showwarning("无分段", "请先设置分割点并创建分段")
            return
        
        try:
            # 从"分段1"格式的字符串中提取数字
            segment_text = self.segment_combobox.get()
            if segment_text.startswith('分段'):
                segment_index = int(segment_text.replace('分段', '')) - 1  # 转换为0基索引
            else:
                segment_index = int(segment_text)
            
            segment = None
            
            # 找到对应的分段
            for seg in self.segments:
                if seg['index'] == segment_index + 1:  # segments从1开始编号
                    segment = seg
                    break
            
            if not segment:
                messagebox.showerror("错误", "未找到对应的分段")
                return
            
            # 保存当前参数
            self.save_current_segment_params(segment_index)
            
            # 获取参数
            if segment_index in self.segment_params:
                params = self.segment_params[segment_index]
            else:
                # 如果没有保存参数，使用当前界面参数
                params = {
                    'min_length': self.segment_min_length.get(),
                    'threshold': self.segment_threshold.get(),
                    'abs_threshold': self.segment_abs_threshold.get(),
                    'reduce_interval': self.segment_reduce_interval.get()
                }
            
            # 直接使用分段内的数据，不需要排序
            segment_sorted_values = np.asarray(segment['data'])
            
            # 对分段数据进行分析
            intervals = self.find_steady_state_intervals(
                segment_sorted_values,
                params['min_length'],
                params['threshold'],
                params['abs_threshold'],
                adaptive=False,
                respect_user_thresholds=True
            )
            
            # 将区间索引转换回全局坐标
            global_intervals = []
            for start_idx, end_idx in intervals:
                global_start = segment['start_idx'] + start_idx
                global_end = segment['start_idx'] + end_idx
                
                if params['reduce_interval']:
                    # 缩减区间边界
                    boundary_reduction = min(5, (global_end - global_start) // 4)
                    global_start += boundary_reduction
                    global_end -= boundary_reduction
                    
                    if global_end > global_start:
                        global_intervals.append((global_start, global_end))
                else:
                    global_intervals.append((global_start, global_end))
            
            # 保存结果到分段
            segment['intervals'] = global_intervals
            
            # 保存全局结果（用于保存等操作）
            self.actual_load_intervals = global_intervals
            self.current_intervals = global_intervals
            
            # 在原图的基础上显示区间划分结果，高亮当前分析段
            self.plot_single_segment_analysis(segment_index, global_intervals, f"分段{segment_index + 1}分析")
            
            # 刷新分段结果表格
            if hasattr(self, 'segment_results_tree'):
                self.refresh_segment_results()
            
            # 更新状态
            self.status_var_actual_load.set(f"分段{segment_index + 1}分析完成! 找到 {len(global_intervals)} 个稳态区间")
            
        except Exception as e:
            messagebox.showerror("分析错误", f"单独分段分析时发生错误:\n{str(e)}")

    def analyze_all_segments_merged(self):
        """分析所有分段并合并结果"""
        if not hasattr(self, 'segments') or not self.segments:
            messagebox.showwarning("无分段", "请先设置分割点并创建分段")
            return
        
        try:
            # 保存当前选中分段的参数
            if hasattr(self, 'segment_combobox') and self.segment_combobox.get():
                try:
                    segment_text = self.segment_combobox.get()
                    if segment_text.startswith('分段'):
                        current_segment_index = int(segment_text.replace('分段', '')) - 1
                        self.save_current_segment_params(current_segment_index)
                except (ValueError, AttributeError):
                    pass
            
            # 确定使用哪种数据
            if self.is_filtered and self.filtered_data is not None:
                data_type = "滤波"
            else:
                data_type = "原始"
            
            total_intervals = []
            
            for i, segment in enumerate(self.segments):
                # 获取分段参数 - 确保使用每个分段保存的具体参数
                if i in self.segment_params:
                    params = self.segment_params[i]
                    min_len = params['min_length']
                    threshold = params['threshold']
                    abs_threshold = params['abs_threshold']
                    reduce_interval = params['reduce_interval']
                else:
                    # 如果没有保存的参数，使用默认参数并提示用户
                    min_len = self.actual_load_min_length.get()
                    threshold = self.actual_current_threshold.get()
                    abs_threshold = self.absolute_threshold.get()
                    reduce_interval = self.reduce_interval_actual_load.get()
                
                # 直接使用分段内的数据，不需要排序
                segment_sorted_values = np.asarray(segment['data'])
                
                # 对分段数据应用稳态区间划分
                intervals = self.find_steady_state_intervals(
                    segment_sorted_values,
                    min_len,
                    threshold,
                    abs_threshold,
                    adaptive=False,
                    respect_user_thresholds=True
                )
                
                # 将区间索引转换回全局坐标
                global_intervals = []
                for start_idx, end_idx in intervals:
                    global_start = segment['start_idx'] + start_idx
                    global_end = segment['start_idx'] + end_idx
                    
                    if reduce_interval:
                        # 缩减区间边界
                        boundary_reduction = min(5, (global_end - global_start) // 4)
                        global_start += boundary_reduction
                        global_end -= boundary_reduction
                        
                        if global_end > global_start:
                            global_intervals.append((global_start, global_end))
                    else:
                        global_intervals.append((global_start, global_end))
                
                segment['intervals'] = global_intervals
                total_intervals.extend(global_intervals)
            
            # 更新主窗口的区间显示
            self.actual_load_intervals = total_intervals
            self.current_intervals = total_intervals
            
            # 重新绘制图表，显示所有分段的合并结果
            self.plot_merged_segments_analysis(f"{data_type}(分段合并分析)")
            
            # 刷新分段结果表格
            if hasattr(self, 'segment_results_tree'):
                self.refresh_segment_results()
            
            # 更新状态
            self.status_var_actual_load.set(f"分段合并分析完成! 总共找到 {len(total_intervals)} 个稳态区间")
            
        except Exception as e:
            messagebox.showerror("分析错误", f"分段合并分析时发生错误:\n{str(e)}")
            
    def copy_global_params_to_segment(self):
        """从整体参数复制到当前选中的分段"""
        try:
            # 更新当前界面参数显示
            self.segment_min_length.set(self.actual_load_min_length.get())
            self.segment_threshold.set(self.actual_current_threshold.get())
            self.segment_abs_threshold.set(self.absolute_threshold.get())
            self.segment_reduce_interval.set(self.reduce_interval_actual_load.get())
            
            # 保存到当前选中的分段
            self.save_current_segment_params_manual()
            
            messagebox.showinfo("成功", "已从整体参数复制并保存到当前分段")
            
        except Exception as e:
            messagebox.showerror("错误", f"复制参数时发生错误:\n{str(e)}")
    
    def save_current_segment_params_manual(self):
        """手动保存当前选中分段的参数"""
        if not hasattr(self, 'segment_combobox') or not self.segment_combobox.get():
            messagebox.showwarning("警告", "请先选择一个分段")
            return
        
        try:
            segment_text = self.segment_combobox.get()
            if segment_text.startswith('分段'):
                segment_index = int(segment_text.replace('分段', '')) - 1
                self.save_current_segment_params(segment_index)
                messagebox.showinfo("成功", f"已保存{segment_text}的参数")
        except Exception as e:
            messagebox.showerror("错误", f"保存参数时发生错误:\n{str(e)}")
    
    def update_segment_combobox(self):
        """更新分段选择下拉框"""
        if hasattr(self, 'segments') and self.segments:
            # 创建分段选项
            segment_count = len(self.segments)
            segment_options = [f"分段{i+1}" for i in range(segment_count)]
            
            # 更新下拉框
            self.segment_combobox['values'] = segment_options
            if segment_count > 0:
                self.segment_combobox.current(0)
                self.on_segment_selected()  # 加载第一个分段的参数
        else:
            self.segment_combobox['values'] = []
            self.segment_combobox.set('')
    
    def update_segment_display(self, event=None):
        """根据选择的显示模式更新分段显示"""
        if not hasattr(self, 'segments') or not self.segments:
            return
        
        mode = self.display_mode_var.get()
        
        try:
            if mode == "all":
                # 显示所有分段的原始数据
                self.plot_steady_intervals("全部分段")
            elif mode == "merged":
                # 显示合并结果
                if all('intervals' in seg for seg in self.segments):
                    self.plot_merged_segments_analysis("合并分析结果")
                else:
                    messagebox.showwarning("警告", "请先执行合并分析")
            elif mode == "single":
                # 显示单个分段
                segment_text = self.display_segment_var.get()
                if segment_text and segment_text.startswith('分段'):
                    segment_index = int(segment_text.replace('分段', '')) - 1
                    segment = None
                    for seg in self.segments:
                        if seg['index'] == segment_index + 1:
                            segment = seg
                            break
                    
                    if segment and 'intervals' in segment:
                        self.plot_single_segment_analysis(segment_index, segment['intervals'], 
                                                         f"分段{segment_index + 1}单独显示")
                    else:
                        messagebox.showwarning("警告", f"分段{segment_index + 1}尚未分析")
        except Exception as e:
            messagebox.showerror("显示错误", f"更新分段显示时发生错误:\n{str(e)}")
    
    def refresh_segment_results(self):
        """刷新分段结果表格"""
        if not hasattr(self, 'segments') or not self.segments:
            return
        
        # 清空现有项目
        for item in self.segment_results_tree.get_children():
            self.segment_results_tree.delete(item)
        
        # 更新显示分段下拉框
        segment_options = [f"分段{i+1}" for i in range(len(self.segments))]
        self.display_segment_combobox['values'] = segment_options
        if segment_options and not self.display_segment_var.get():
            self.display_segment_combobox.current(0)
        
        # 添加分段结果到表格
        for i, segment in enumerate(self.segments):
            segment_name = f"分段{i+1}"
            
            # 获取参数设置
            if i in self.segment_params:
                params = self.segment_params[i]
                param_str = f"长度:{params['min_length']}, 阈值:{params['threshold']:.2f}, 绝对:{params['abs_threshold']:.2f}"
            else:
                param_str = "未设置"
            
            # 获取稳态区间信息
            if 'intervals' in segment and segment['intervals']:
                intervals = segment['intervals']
                interval_count = len(intervals)
                
                # 区间详情（简化显示）
                if len(intervals) <= 3:
                    detail_str = ", ".join([f"[{s},{e}]" for s, e in intervals])
                else:
                    detail_str = f"[{intervals[0][0]},{intervals[0][1]}], ... +{len(intervals)-1}个"
            else:
                interval_count = 0
                detail_str = "未分析"
            
            # 插入行
            self.segment_results_tree.insert('', 'end', values=(
                segment_name, param_str, interval_count, detail_str
            ))
        
        # 更新状态
        self.status_var_actual_load.set(f"已刷新 {len(self.segments)} 个分段的结果信息")
    
    def export_segment_details(self):
        """导出分段详细信息"""
        if not hasattr(self, 'segments') or not self.segments:
            messagebox.showwarning("无数据", "没有分段数据可导出")
            return
        
        try:
            from tkinter import filedialog
            filename = filedialog.asksaveasfilename(
                title="保存分段详情",
                defaultextension=".txt",
                filetypes=[("文本文件", "*.txt"), ("CSV文件", "*.csv"), ("所有文件", "*.*")]
            )
            
            if not filename:
                return
            
            with open(filename, 'w', encoding='utf-8') as f:
                f.write("分段稳态区间分析详细报告\n")
                f.write("=" * 50 + "\n\n")
                
                for i, segment in enumerate(self.segments):
                    f.write(f"分段{i+1}:\n")
                    f.write(f"  数据范围: [{segment['start_idx']}, {segment['end_idx']}]\n")
                    
                    # 参数信息
                    if i in self.segment_params:
                        params = self.segment_params[i]
                        f.write(f"  参数设置:\n")
                        f.write(f"    最小区间长度: {params['min_length']}\n")
                        f.write(f"    波动阈值: {params['threshold']:.2f}\n")
                        f.write(f"    绝对波动阈值: {params['abs_threshold']:.2f}\n")
                        f.write(f"    缩减区间边界: {params['reduce_interval']}\n")
                    else:
                        f.write(f"  参数设置: 未配置\n")
                    
                    # 稳态区间信息
                    if 'intervals' in segment and segment['intervals']:
                        intervals = segment['intervals']
                        f.write(f"  稳态区间数量: {len(intervals)}\n")
                        f.write(f"  区间详情:\n")
                        for j, (start_idx, end_idx) in enumerate(intervals, 1):
                            if start_idx < len(self.actual_load_data):
                                # 获取程序行号和点数索引
                                if (hasattr(self, 'actual_load_line_numbers') and 
                                    hasattr(self, 'actual_load_point_indices') and
                                    start_idx < len(self.actual_load_line_numbers) and
                                    end_idx < len(self.actual_load_line_numbers)):
                                    start_ln = self.actual_load_line_numbers[start_idx]
                                    start_point_idx = self.actual_load_point_indices[start_idx]
                                    end_ln = self.actual_load_line_numbers[end_idx]
                                    end_point_idx = self.actual_load_point_indices[end_idx]
                                    f.write(f"    区间{j}: {start_ln:.0f}.{start_point_idx} - {end_ln:.0f}.{end_point_idx} [索引:{start_idx}-{end_idx}]\n")
                                else:
                                    f.write(f"    区间{j}: [索引:{start_idx}-{end_idx}]\n")
                    else:
                        f.write(f"  稳态区间数量: 0 (未分析)\n")
                    
                    f.write("\n")
            
            messagebox.showinfo("成功", f"分段详情已导出到: {filename}")
            
        except Exception as e:
            messagebox.showerror("导出错误", f"导出分段详情时发生错误:\n{str(e)}")
    
    def on_segment_result_double_click(self, event):
        """双击分段结果表格项时的处理"""
        item = self.segment_results_tree.selection()[0]
        segment_name = self.segment_results_tree.item(item, "values")[0]
        
        # 设置显示模式为单独，并选择对应分段
        self.display_mode_var.set("single")
        self.display_segment_var.set(segment_name)
        
        # 更新显示
        self.update_segment_display()
    
    def setup_tech_theme(self):
        """配置科技感主题样式"""
        style = ttk.Style()
        
        # 设置主题为clam（比较容易自定义）
        try:
            style.theme_use('clam')
        except:
            pass
        
        # 配置按钮样式 - 科技感蓝色
        style.configure('Tech.TButton',
                       background='#0066cc',
                       foreground='white',
                       font=('Microsoft YaHei UI', 11, 'bold'),
                       borderwidth=0,
                       focuscolor='none',
                       padding=(20, 10))
        
        style.map('Tech.TButton',
                 background=[('active', '#0088ff'), ('pressed', '#004499')],
                 foreground=[('active', 'white'), ('pressed', 'white')])
        
        # 配置主要操作按钮样式 - 霓虹绿
        style.configure('Primary.TButton',
                       background='#00cc66',
                       foreground='white',
                       font=('Microsoft YaHei UI', 12, 'bold'),
                       borderwidth=0,
                       focuscolor='none',
                       padding=(25, 12))
        
        style.map('Primary.TButton',
                 background=[('active', '#00ff88'), ('pressed', '#009944')],
                 foreground=[('active', 'white'), ('pressed', 'white')])
        
        # 配置危险操作按钮 - 橙红色
        style.configure('Danger.TButton',
                       background='#ff6600',
                       foreground='white',
                       font=('Microsoft YaHei UI', 11, 'bold'),
                       borderwidth=0,
                       focuscolor='none',
                       padding=(20, 10))
        
        style.map('Danger.TButton',
                 background=[('active', '#ff8833'), ('pressed', '#cc5200')],
                 foreground=[('active', 'white'), ('pressed', 'white')])
        
        # 配置标签框样式
        style.configure('Tech.TLabelframe',
                       background='#f0f4f8',
                       foreground='#2c3e50',
                       font=('Microsoft YaHei UI', 10, 'bold'),
                       borderwidth=2,
                       relief='groove')
        
        style.configure('Tech.TLabelframe.Label',
                       background='#f0f4f8',
                       foreground='#0066cc',
                       font=('Microsoft YaHei UI', 11, 'bold'))
    
    def apply_tech_theme_to_axes(self, ax):
        """应用主题到坐标轴"""
        # 设置白色背景
        ax.set_facecolor('white')
        
        # 设置坐标轴边框颜色
        for spine in ax.spines.values():
            spine.set_edgecolor('#333333')
            spine.set_linewidth(1.5)
        
        # 设置刻度颜色
        ax.tick_params(axis='both', colors='#333333', labelsize=12)
        
        # 设置网格
        ax.grid(True, linestyle=':', alpha=0.3, linewidth=0.5, color='gray', zorder=0)
    
    def apply_tech_theme_to_figure(self, fig, ax, title):
        """应用主题到整个图表"""
        # 设置图表背景为白色
        fig.patch.set_facecolor('white')
        
        # 应用坐标轴主题
        self.apply_tech_theme_to_axes(ax)
        
        # 设置标题样式
        ax.set_title(title, fontsize=18, fontweight='bold', color='#333333', pad=15)
        
        # 设置轴标签颜色和大小
        ax.set_xlabel(ax.get_xlabel(), fontsize=14, fontweight='bold', color='#333333')
        ax.set_ylabel(ax.get_ylabel(), fontsize=14, fontweight='bold', color='#333333')
        
        # 调整布局以居中对称
        fig.subplots_adjust(left=0.10, right=0.90, top=0.94, bottom=0.08)
    
    def setup_chart_interactions(self):
        """设置图表交互功能（缩放、滚动等）"""
        # 为实际负载图表添加滚动缩放功能
        self.scroll_cid = self.canvas_actual_load.mpl_connect('scroll_event', self.on_scroll_zoom)
        
        # 保存原始视图范围（在数据加载后调用）
        if hasattr(self, 'ax_actual_load') and self.ax_actual_load.get_xlim() != (0.0, 1.0):
            self.original_xlim = self.ax_actual_load.get_xlim()
            self.original_ylim = self.ax_actual_load.get_ylim()
    
    def on_scroll_zoom(self, event):
        """处理鼠标滚轮缩放事件"""
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
        
        # 只缩放x轴（横向缩放）
        new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
        
        relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0])
        
        new_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
        
        # 应用新的坐标轴范围（只改变x轴）
        self.ax_actual_load.set_xlim(new_xlim)
        
        # 重绘图表
        self.canvas_actual_load.draw()
    
    def on_data_scroll_zoom(self, event):
        """数据处理标签页图表缩放：
        - 默认：横向缩放(X轴)
        - Ctrl + 滚轮：纵向缩放(Y轴)
        - Shift + 滚轮：同时缩放(X+Y)
        """
        fig = getattr(self, '_current_preview_fig', None)
        if fig is None or not getattr(fig, 'axes', None):
            return
        if event.inaxes is None or event.inaxes not in fig.axes:
            return

        # 允许无 self.data 的情况下也能缩放（只要图已经渲染出来）
        base_ax = self.ax_data if self.ax_data in fig.axes else fig.axes[0]

        key = (getattr(event, 'key', '') or '')
        key_l = key.lower()

        zoom_x = True
        zoom_y = False
        if 'control' in key_l or 'ctrl' in key_l:
            zoom_x = False
            zoom_y = True
        if 'shift' in key_l:
            zoom_x = True
            zoom_y = True

        # 缩放倍率
        if event.button == 'up':
            scale_factor = 0.9
        elif event.button == 'down':
            scale_factor = 1.1
        else:
            return

        # 鼠标所在数据坐标
        xdata = event.xdata
        ydata = event.ydata

        # X轴缩放
        if zoom_x and xdata is not None:
            cur_xlim = base_ax.get_xlim()
            new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
            relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0]) if (cur_xlim[1] - cur_xlim[0]) != 0 else 0.5
            new_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
            for ax in fig.axes:
                try:
                    ax.set_xlim(new_xlim)
                except Exception:
                    pass

        # Y轴缩放（只对当前inaxes与共享y轴的轴生效通常更合理，但这里先简单对base_ax应用）
        if zoom_y and ydata is not None:
            cur_ylim = event.inaxes.get_ylim()
            new_height = (cur_ylim[1] - cur_ylim[0]) * scale_factor
            rely = (cur_ylim[1] - ydata) / (cur_ylim[1] - cur_ylim[0]) if (cur_ylim[1] - cur_ylim[0]) != 0 else 0.5
            new_ylim = [ydata - new_height * (1 - rely), ydata + new_height * rely]
            try:
                event.inaxes.set_ylim(new_ylim)
            except Exception:
                pass

        try:
            self.canvas_data.draw_idle()
        except Exception:
            pass

    def reset_chart_view(self):
        """重置图表视图到原始范围"""
        if self.original_xlim is not None and self.original_ylim is not None:
            self.ax_actual_load.set_xlim(self.original_xlim)
            self.ax_actual_load.set_ylim(self.original_ylim)
            self.canvas_actual_load.draw()
            self.status_var_actual_load.set("图表视图已重置")
        else:
            messagebox.showinfo("提示", "没有可重置的视图范围，请先加载数据")
    
    def setup_steady_chart_interactions(self):
        """设置稳态区间图表的交互功能"""
        try:
            # 为时域图表设置交互
            if hasattr(self, 'steady_time_scroll_connection'):
                self.canvas_steady_time.mpl_disconnect(self.steady_time_scroll_connection)
            
            self.steady_time_scroll_connection = self.canvas_steady_time.mpl_connect('scroll_event', self.on_steady_time_scroll)
            
            # 为指令域图表设置交互
            if hasattr(self, 'steady_n_scroll_connection'):
                self.canvas_steady_n.mpl_disconnect(self.steady_n_scroll_connection)
            
            self.steady_n_scroll_connection = self.canvas_steady_n.mpl_connect('scroll_event', self.on_steady_n_scroll)
            
            # 保存原始视图范围
            if hasattr(self, 'ax_steady_time') and self.ax_steady_time.get_xlim() != (0.0, 1.0):
                self.original_steady_time_xlim = self.ax_steady_time.get_xlim()
                self.original_steady_time_ylim = self.ax_steady_time.get_ylim()
            
            if hasattr(self, 'ax_steady_n') and self.ax_steady_n.get_xlim() != (0.0, 1.0):
                self.original_steady_n_xlim = self.ax_steady_n.get_xlim()
                self.original_steady_n_ylim = self.ax_steady_n.get_ylim()
        except Exception as e:
            print(f"设置稳态图表交互时出错: {e}")
    
    def on_steady_time_scroll(self, event):
        """处理稳态时域图表的鼠标滚轮缩放事件"""
        if event.inaxes != self.ax_steady_time:
            return
        
        self._handle_chart_scroll(event, self.ax_steady_time, self.canvas_steady_time)
    
    def on_steady_n_scroll(self, event):
        """处理稳态指令域图表的鼠标滚轮缩放事件"""
        if event.inaxes != self.ax_steady_n:
            return
        
        self._handle_chart_scroll(event, self.ax_steady_n, self.canvas_steady_n)
    
    def _handle_chart_scroll(self, event, ax, canvas):
        """通用的图表滚轮缩放处理函数"""
        # 获取当前坐标轴范围
        cur_xlim = ax.get_xlim()
        cur_ylim = ax.get_ylim()
        
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
        
        # 计算新的坐标轴范围
        new_width = (cur_xlim[1] - cur_xlim[0]) * scale_factor
        new_height = (cur_ylim[1] - cur_ylim[0]) * scale_factor
        
        relx = (cur_xlim[1] - xdata) / (cur_xlim[1] - cur_xlim[0])
        rely = (cur_ylim[1] - ydata) / (cur_ylim[1] - cur_ylim[0])
        
        new_xlim = [xdata - new_width * (1 - relx), xdata + new_width * relx]
        new_ylim = [ydata - new_height * (1 - rely), ydata + new_height * rely]
        
        # 设置新的坐标轴范围
        ax.set_xlim(new_xlim)
        ax.set_ylim(new_ylim)
        
        # 重绘图表
        canvas.draw()
    
    def reset_steady_chart_view(self):
        """重置稳态图表的视图范围"""
        try:
            # 重置时域图表
            if hasattr(self, 'original_steady_time_xlim') and hasattr(self, 'original_steady_time_ylim'):
                self.ax_steady_time.set_xlim(self.original_steady_time_xlim)
                self.ax_steady_time.set_ylim(self.original_steady_time_ylim)
                self.canvas_steady_time.draw()
            
            # 重置指令域图表
            if hasattr(self, 'original_steady_n_xlim') and hasattr(self, 'original_steady_n_ylim'):
                self.ax_steady_n.set_xlim(self.original_steady_n_xlim)
                self.ax_steady_n.set_ylim(self.original_steady_n_ylim)
                self.canvas_steady_n.draw()
            
            messagebox.showinfo("成功", "稳态图表视图已重置")
        except Exception as e:
            messagebox.showerror("错误", f"重置稳态图表视图时出错: {str(e)}")
    
    def adjust_actual_load_chart_size(self):
        """专门调整实际负载图表以填充整个可用区域"""
        try:
            if not hasattr(self, 'actual_load_figure_frame') or not hasattr(self, 'fig_actual_load'):
                return
                
            # 获取图表框架的实际尺寸
            self.actual_load_figure_frame.update_idletasks()
            frame_width = self.actual_load_figure_frame.winfo_width()
            frame_height = self.actual_load_figure_frame.winfo_height()
            
            if frame_width > 1 and frame_height > 1:  # 确保框架已完全初始化
                # 根据框架尺寸计算合适的图表大小
                dpi = self.fig_actual_load.dpi
                fig_width = max(6, frame_width / dpi)
                fig_height = max(4, (frame_height - 50) / dpi)  # 减去工具栏高度
                
                # 设置图表大小
                self.fig_actual_load.set_size_inches(fig_width, fig_height)
                
                # 重新调整子图边距 - 使用优化后的边距
                self.fig_actual_load.subplots_adjust(
                    left=0.08, bottom=0.10, right=0.96, top=0.94,
                    wspace=0.15, hspace=0.15
                )
                
                # 重绘画布
                self.canvas_actual_load.draw_idle()
                
        except Exception as e:
            # 静默处理异常
            pass

    def on_window_resize(self, event):
        """处理窗口大小变化事件 - 添加防抖动机制"""
        # 只处理主窗口的resize事件，避免子组件的resize事件
        if event.widget == self.root:
            # 取消之前的定时器
            if self._resize_timer is not None:
                self.root.after_cancel(self._resize_timer)
            # 设置新的延迟调用（300ms延迟，避免拖拽时频繁调用）
            self._resize_timer = self.root.after(300, self._do_resize)
    
    def _do_resize(self):
        """实际执行resize操作"""
        self._resize_timer = None
        self.adjust_figure_sizes()
        self.adjust_actual_load_chart_size()
    
    def adjust_figure_sizes(self):
        """根据当前窗口大小调整图表大小 - 让图表随容器实时放缩、尽量铺满"""
        try:
            # 优先用当前图表canvas的实际像素尺寸（比LabelFrame更准）
            w = h = 0
            if hasattr(self, 'canvas_data') and self.canvas_data is not None:
                try:
                    tw = self.canvas_data.get_tk_widget()
                    w = tw.winfo_width()
                    h = tw.winfo_height()
                except Exception:
                    w = h = 0

            if (w < 50 or h < 50) and hasattr(self, 'data_figure_frame'):
                w = self.data_figure_frame.winfo_width()
                h = self.data_figure_frame.winfo_height()

            # 容器还未完全初始化
            if w < 50 or h < 50:
                return

            # 给Tk控件边框/内边距留一点点余量（太大就会“看着缩”）
            w_px = max(10, int(w) - 6)
            h_px = max(10, int(h) - 6)

            # 1) 工艺信息分析页：当前预览图（以及缓存图）统一跟随预览区域大小
            if hasattr(self, 'figures') and self.figures:
                for fig in self.figures:
                    try:
                        dpi = float(fig.get_dpi()) if fig.get_dpi() else 100.0
                    except Exception:
                        dpi = 100.0
                    fig.set_size_inches(w_px / dpi, h_px / dpi, forward=True)
                    # tight_layout 的 pad 过大会显得“没铺满”
                    try:
                        fig.tight_layout(pad=0.6)
                    except Exception:
                        pass

            # 2) 直接重绘当前预览canvas（之前只在 fig_data 存在时重绘，导致“看起来不缩放”）
            if hasattr(self, 'canvas_data') and self.canvas_data is not None:
                self.canvas_data.draw_idle()

            # 3) 其他标签页图表（保持原逻辑，但减少边距）
            if hasattr(self, 'fig_actual_load'):
                try:
                    dpi = float(self.fig_actual_load.get_dpi()) if self.fig_actual_load.get_dpi() else 100.0
                except Exception:
                    dpi = 100.0
                self.fig_actual_load.set_size_inches(w_px / dpi, h_px / dpi, forward=True)
                try:
                    self.fig_actual_load.tight_layout(pad=0.6)
                except Exception:
                    pass
                if hasattr(self, 'canvas_actual_load'):
                    self.canvas_actual_load.draw_idle()

            # 左右布局图表维持略小比例
            steady_w_px = int(w_px * 0.92)
            steady_h_px = int(h_px * 0.92)

            def _resize_other(fig_attr, canvas_attr):
                if hasattr(self, fig_attr):
                    fig = getattr(self, fig_attr)
                    if fig is None:
                        return
                    try:
                        dpi = float(fig.get_dpi()) if fig.get_dpi() else 100.0
                    except Exception:
                        dpi = 100.0
                    fig.set_size_inches(steady_w_px / dpi, steady_h_px / dpi, forward=True)
                    try:
                        fig.tight_layout(pad=0.6)
                    except Exception:
                        pass
                    if hasattr(self, canvas_attr):
                        getattr(self, canvas_attr).draw_idle()

            _resize_other('fig_steady_time', 'canvas_steady_time')
            _resize_other('fig_steady_freq', 'canvas_steady_freq')
            _resize_other('fig_steady_n', 'canvas_steady_n')

        except Exception:
            # 静默处理异常，避免影响程序运行
            pass

def optimize_memory():
    """优化内存使用和性能"""
    # 减少垃圾回收频率
    gc.set_threshold(10000, 10, 10)
    
    # 提高文件操作缓冲区
    sys.stderr = open(os.devnull, 'w') if not sys.stderr else sys.stderr
    sys.stdout = open(os.devnull, 'w') if not sys.stdout else sys.stdout

if __name__ == "__main__":
    optimize_memory()
    root = tk.Tk()
    
    # 添加一些样式美化
    style = ttk.Style()
    style.configure("Accent.TButton", font=('Arial', 10, 'bold'), foreground='white', background='#0078D7')
    style.map("Accent.TButton", background=[('active', '#005499')])
    
    # 创建应用实例
    app = MillingAnalysisTool(root)
    
    # 在应用创建完成后，延迟调整图表大小
    root.after(100, app.adjust_figure_sizes)
    
    root.mainloop()
