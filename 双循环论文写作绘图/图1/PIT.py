import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib import rcParams

rcParams['font.family'] = 'serif'
rcParams['font.serif'] = ['Times New Roman']
rcParams['font.size'] = 8  # 小图适配字号

def generate_pit_small_hd():
    headers = ["ID", "Range", "Geo", "Imp.$\hat{Z}$", "Feed $F$", "state"]
    rows = [
        {"id": "#101", "r": "0-15", "g": "(3,10)", "z": 2.05, "zm":4, "zc":"#4CAF50", "f": 5000, "fm":6000, "fc":"#1976D2", "s":"Norm"},
        {"id": "#102", "r": "15-28", "g": "(3,10)", "z": 3.60, "zm":4, "zc":"#D32F2F", "f": 4200, "fm":6000, "fc":"#90CAF9", "s":"Hard"},
        {"id": "#103", "r": "28-45", "g": "(3,10)", "z": 0.80, "zm":4, "zc":"#2196F3", "f": 6500, "fm":8000, "fc":"#0D47A1", "s":"Soft"}
    ]
    
    # 3.2 英寸宽，适配单栏
    fig, ax = plt.subplots(figsize=(3.2, 1.8), dpi=600)
    ax.set_axis_off()
    
    # 参数调整
    row_h = 1.0; head_h = 1.0
    cols = [0.7, 1.0, 1.0, 1.4, 1.4, 0.8]
    total_w = sum(cols)
    sx, sy = 0, 4
    
    # 表头
    cx = sx
    for i, txt in enumerate(headers):
        rect = patches.Rectangle((cx, sy), cols[i], head_h, fc='#F5F5F5', ec='none')
        ax.add_patch(rect)
        ax.text(cx + cols[i]/2, sy + head_h/2, txt, ha='center', va='center', fontweight='bold', fontsize=7.5)
        cx += cols[i]
        
    ax.plot([sx, sx+total_w], [sy+head_h, sy+head_h], color='black', lw=1.2)
    ax.plot([sx, sx+total_w], [sy, sy], color='black', lw=0.8)
    
    # 数据行
    y = sy
    for ridx, row in enumerate(rows):
        y -= row_h
        cx = sx
        vals = [row["id"], row["r"], row["g"], "", "", row["s"]]
        
        for cidx, val in enumerate(vals):
            if cidx not in [3,4]:
                color='black'; weight='normal'
                if cidx==5:
                    if val=="Hard": color='#D32F2F'; weight='bold'
                    elif val=="Soft": color='#1976D2'; weight='bold'
                    else: color='#2E7D32'
                ax.text(cx+cols[cidx]/2, y+row_h/2, val, ha='center', va='center', color=color, fontweight=weight, fontsize=7.5)
            
            elif cidx in [3,4]:
                bg = patches.Rectangle((cx+0.1, y+0.2), cols[cidx]-0.2, 0.6, fc='#ECEFF1', ec='none')
                ax.add_patch(bg)
                key_val = "z" if cidx==3 else "f"
                key_max = "zm" if cidx==3 else "fm"
                key_col = "zc" if cidx==3 else "fc"
                w = (row[key_val]/row[key_max]) * (cols[cidx]-0.2)
                bar = patches.Rectangle((cx+0.1, y+0.2), w, 0.6, fc=row[key_col], ec='none')
                ax.add_patch(bar)
                txt_val = f"{row[key_val]:.2f}" if cidx==3 else f"{row[key_val]}"
                ax.text(cx+cols[cidx]/2, y+0.5, txt_val, ha='center', va='center', fontsize=7, fontweight='bold')
                
            cx += cols[cidx]
        
        if ridx < len(rows)-1:
            ax.plot([sx, sx+total_w], [y, y], color='#CFD8DC', lw=0.4)

    # 截断符
    by = y
    ax.plot([sx, sx+total_w], [by, by], color='black', lw=0.8)
    ax.text(sx + total_w/2, by - 0.3, "...", ha='center', va='center', fontsize=12, color='gray', fontweight='bold')
    
    def draw_break(bx):
        ax.plot([bx, bx+0.1], [by-0.15, by+0.15], color='black', lw=0.8)
        ax.plot([bx+0.05, bx+0.15], [by-0.15, by+0.15], color='black', lw=0.8)
    draw_break(sx - 0.1)
    draw_break(sx + total_w - 0.15)

    ax.set_xlim(sx-0.2, sx+total_w+0.2)
    ax.set_ylim(by-0.5, sy+head_h+0.1)
    
    plt.subplots_adjust(left=0, right=1, bottom=0, top=1)
    plt.savefig("pit_small_hd.png", transparent=True, bbox_inches='tight', pad_inches=0, dpi=600)
    plt.savefig("pit_small_hd.pdf", transparent=True, bbox_inches='tight', pad_inches=0)
    plt.show()

if __name__ == "__main__":
    generate_pit_small_hd()