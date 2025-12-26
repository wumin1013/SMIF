import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import LineCollection
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib import rcParams

# 字体与字号设置 (保持视觉平衡)
rcParams['font.family'] = 'serif'
rcParams['font.serif'] = ['Times New Roman']
rcParams['font.size'] = 13

def generate_strategy_b_multipass_linear():
    # 画布设置
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(3.5, 2.8), dpi=300)
    plt.subplots_adjust(hspace=0.65) 

    # ==========================================
    # 通用数据
    # ==========================================
    s = np.linspace(0, 100, 500)
    colors = [(0.0, '#D32F2F'), (0.45, '#43A047'), (0.55, '#43A047'), (1.0, '#1976D2')]
    cmap_speed = LinearSegmentedColormap.from_list("SpeedMap", colors)
    
    # ==========================================
    # 子图 1: B0 - 进给速度 (保持完美状态)
    # ==========================================
    ax1.set_title("Strategy B0: Feed Planning ($F$)", loc='left', fontsize=12, fontweight='bold', pad=10)
    ax1.set_axis_off()
    ax1.add_patch(plt.Rectangle((0, -1.5), 100, 3, fc='#F9F9F9', ec='none'))
    
    F_vals = np.ones_like(s) * 0.5
    mask_dec = (s > 20) & (s < 40)
    F_vals[mask_dec] = 0.5 - 0.5 * np.sin((s[mask_dec]-20)/(20)*np.pi)**2
    mask_acc = (s > 60) & (s < 80)
    F_vals[mask_acc] = 0.5 + 0.5 * np.sin((s[mask_acc]-60)/(20)*np.pi)**2
    
    points = np.array([s, np.zeros_like(s)]).T.reshape(-1, 1, 2)
    segments = np.concatenate([points[:-1], points[1:]], axis=1)
    lc1 = LineCollection(segments, cmap=cmap_speed, norm=Normalize(0, 1))
    lc1.set_array(F_vals)
    lc1.set_linewidth(5.0)
    ax1.add_collection(lc1)
    
    # B0 标注
    ax1.annotate(r"$F \downarrow$ Slow", xy=(30, 0), xytext=(30, 1.3),
                 arrowprops=dict(arrowstyle='->', color='#D32F2F', lw=1.5),
                 color='#D32F2F', ha='center', fontweight='bold')
    ax1.text(30, -0.9, "High Z", color='#D32F2F', ha='center', fontsize=11)
    
    ax1.annotate(r"$F \uparrow$ Fast", xy=(70, 0), xytext=(70, 1.3),
                 arrowprops=dict(arrowstyle='->', color='#1976D2', lw=1.5),
                 color='#1976D2', ha='center', fontweight='bold')
    ax1.text(70, -0.9, "Low Z", color='#1976D2', ha='center', fontsize=11)
    ax1.text(50, 0.4, "Base Speed", color='#388E3C', ha='center', fontsize=10)
    ax1.set_xlim(-5, 105); ax1.set_ylim(-2, 2.6)

    # ==========================================
    # 子图 2: B1 - 局部多道次 (Local Multi-pass)
    # ==========================================
    ax2.set_title("Strategy B1: Path Re-planning", loc='left', fontsize=12, fontweight='bold', pad=10)
    ax2.set_axis_off()
    
    # 1. 切削范围边界 (Fixed Cutting Range)
    boundary_w = 1.0
    ax2.plot([0, 100], [boundary_w, boundary_w], color='gray', ls='--', lw=0.8, alpha=0.5)
    ax2.plot([0, 100], [-boundary_w, -boundary_w], color='gray', ls='--', lw=0.8, alpha=0.5)
    ax2.text(2, -boundary_w - 0.7, "Fixed Cutting Range", color='gray', fontsize=8, ha='left')

    # 2. 构造分流轨迹
    # 使用 Sigmoid 函数实现平滑分流
    def sigmoid_blend(t):
        return 1 / (1 + np.exp(-10 * (t - 0.5)))

    # --- High Z (Red) 区: 平行分流 (Parallel Multi-pass) ---
    # 区间 20-40。我们在 20-25 分流，25-35 平行，35-40 汇合
    x_split_start, x_split_end = 20, 25
    x_merge_start, x_merge_end = 35, 40
    split_h = 0.6 # 分流高度
    
    # 上路轨迹 (Upper Path)
    s_upper = np.linspace(20, 40, 100)
    y_upper = np.zeros_like(s_upper)
    
    # 分流段
    mask1 = (s_upper >= 20) & (s_upper < 25)
    t1 = (s_upper[mask1] - 20) / 5
    y_upper[mask1] = split_h * sigmoid_blend(t1)
    
    # 平行段
    mask2 = (s_upper >= 25) & (s_upper < 35)
    y_upper[mask2] = split_h
    
    # 汇合段
    mask3 = (s_upper >= 35) & (s_upper <= 40)
    t3 = (s_upper[mask3] - 35) / 5
    y_upper[mask3] = split_h * (1 - sigmoid_blend(t3))
    
    # 下路轨迹 (Lower Path) - 对称
    y_lower = -y_upper
    
    # 绘制分流线 (Red)
    ax2.plot(s_upper, y_upper, color='#D32F2F', lw=2.2)
    ax2.plot(s_upper, y_lower, color='#D32F2F', lw=2.2)
    
    # --- Low Z (Blue) 区: 粗直线 ---
    ax2.plot([60, 80], [0, 0], color='#1976D2', lw=6.5, alpha=0.9, solid_capstyle='butt') 
    
    # --- Normal (Green) 连接 ---
    ax2.plot([0, 20], [0, 0], color='#43A047', lw=3.0)
    ax2.plot([40, 60], [0, 0], color='#43A047', lw=3.0)
    ax2.plot([80, 100], [0, 0], color='#43A047', lw=3.0)
    
    # --- 标注 ---
    # Multi-pass
    ax2.text(30, 1.5, "Multi-pass", color='#D32F2F', ha='center', va='center', 
             fontweight='bold', zorder=20)
    
    # Wider ae
    ax2.text(70, 1.5, r"Wider $a_e$", color='blue', ha='center', va='center', 
             fontsize=11, fontweight='bold', zorder=20)
    
    # 连接点
    ax2.scatter([20, 40, 60, 80], [0, 0, 0, 0], color='black', s=15, zorder=10)

    # 坐标轴
    ax2.annotate("", xy=(100, -1.8), xytext=(0, -1.8), arrowprops=dict(arrowstyle='->', color='black', lw=1.2))
    ax2.text(50, -2.5, r"Stroke Position $s$", ha='center', fontsize=11)
    
    ax2.set_xlim(-5, 105)
    ax2.set_ylim(-2.8, 2.8)

    plt.tight_layout()
    plt.savefig("strategy_b_multipass_linear.pdf", transparent=True, bbox_inches='tight', pad_inches=0.05)
    plt.show()

if __name__ == "__main__":
    generate_strategy_b_multipass_linear()