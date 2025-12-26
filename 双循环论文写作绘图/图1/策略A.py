import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib import rcParams

# --- 核心设置：字号加大 ---
rcParams['font.family'] = 'serif'
rcParams['font.serif'] = ['Times New Roman']
rcParams['font.size'] = 13  # 全局字号从 11 提升至 13

def generate_strategy_a_tristate_titled():
    # 画布设置：3.5 x 3.2 英寸 (高度增加以容纳标题)
    fig, ax = plt.subplots(figsize=(3.5, 3.2), dpi=300)
    ax.set_axis_off()
    
    # --- 添加标题 ---
    # 使用与 Strategy B 相同的左对齐粗体风格
    ax.set_title("Strategy A: Global Layering", loc='left', fontsize=14, fontweight='bold', pad=12)
    
    # 参数
    x_pos = 0.5
    width = 2.0
    depth = 0.6 # 侧面深度
    
    # 层结构定义：Normal(绿) -> Hard(红) -> Soft(蓝)
    layers = [
        # 1. 底部：Normal (基准) - Green
        {"h": 0.45, "c": "#66BB6A", "type": "Norm"}, 
        {"h": 0.45, "c": "#66BB6A", "type": "Norm"},
        {"h": 0.45, "c": "#66BB6A", "type": "Norm"},
        
        # 2. 中间：Hard (硬点) - Red - 变薄
        {"h": 0.25, "c": "#EF5350", "type": "Hard"}, 
        {"h": 0.25, "c": "#EF5350", "type": "Hard"},
        {"h": 0.25, "c": "#EF5350", "type": "Hard"},
        {"h": 0.25, "c": "#EF5350", "type": "Hard"},
        
        # 3. 顶部：Soft (软区) - Blue - 变厚
        {"h": 0.70, "c": "#42A5F5", "type": "Soft"}, 
        {"h": 0.70, "c": "#42A5F5", "type": "Soft"},
    ]
    
    current_y = 0.2
    
    # --- 绘制堆叠层 ---
    for layer in layers:
        # 正面矩形
        rect = patches.Rectangle((x_pos, current_y), width, layer["h"], 
                                 facecolor=layer["c"], edgecolor='white', linewidth=0.8, alpha=0.95)
        ax.add_patch(rect)
        
        # 侧面投影 (2.5D效果)
        poly_side = patches.Polygon([
            [x_pos + width, current_y],
            [x_pos + width + depth, current_y + depth*0.5],
            [x_pos + width + depth, current_y + layer["h"] + depth*0.5],
            [x_pos + width, current_y + layer["h"]]
        ], facecolor=layer["c"], edgecolor='white', linewidth=0.4, alpha=0.7)
        ax.add_patch(poly_side)
        
        current_y += layer["h"]

    # 顶盖
    top_y = current_y
    poly_top = patches.Polygon([
        [x_pos, top_y],
        [x_pos + width, top_y],
        [x_pos + width + depth, top_y + depth*0.5],
        [x_pos + depth, top_y + depth*0.5]
    ], facecolor='#BBDEFB', edgecolor='white', linewidth=0.8, alpha=0.6) # 浅蓝顶盖
    ax.add_patch(poly_top)

    # --- 标注 (Annotate) - 字号加大 ---
    arrow_args = dict(arrowstyle='->', lw=1.5) # 箭头加粗
    text_x = x_pos + width + depth + 0.1
    
    # 1. Normal (Green)
    norm_y = 0.2 + 0.45 * 1.5
    ax.annotate(r"Normal $Z$", 
                xy=(x_pos+width+depth, norm_y), xytext=(text_x, norm_y),
                arrowprops=dict(**arrow_args, color='#2E7D32'),
                color='#2E7D32', fontweight='bold', va='center', fontsize=12) # 9->12
    ax.text(text_x, norm_y - 0.25, r"($a_p$ Base)", fontsize=11, color='#2E7D32') # 8->11

    # 2. Hard (Red)
    hard_y = 0.2 + 0.45*3 + 0.25*2
    ax.annotate(r"High $Z$", 
                xy=(x_pos+width+depth, hard_y), xytext=(text_x, hard_y),
                arrowprops=dict(**arrow_args, color='#D32F2F'),
                color='#D32F2F', fontweight='bold', va='center', fontsize=12)
    ax.text(text_x, hard_y - 0.25, r"($a_p \downarrow$ Thin)", fontsize=11, color='#D32F2F')

    # 3. Soft (Blue)
    soft_y = top_y - 0.7/2 - 0.2
    ax.annotate(r"Low $Z$", 
                xy=(x_pos+width+depth, soft_y), xytext=(text_x, soft_y),
                arrowprops=dict(**arrow_args, color='#1565C0'),
                color='#1565C0', fontweight='bold', va='center', fontsize=12)
    ax.text(text_x, soft_y - 0.25, r"($a_p \uparrow$ Thick)", fontsize=11, color='#1565C0')
    
    # 裁剪
    ax.set_xlim(0, 5.0) # 稍微加宽以容纳大号字体
    ax.set_ylim(0, top_y + 0.5)
    plt.subplots_adjust(left=0, right=1, bottom=0, top=1)
    
    plt.savefig("strategy_a_titled.pdf", transparent=True, bbox_inches='tight')
    plt.show()

if __name__ == "__main__":
    generate_strategy_a_tristate_titled()