import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Line3DCollection, Poly3DCollection
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.widgets import Button
import time

def generate_smif_small_hd_interactive():
    # --- 1. 数据生成 (保持不变) ---
    def generate_path(width, height, radius, n_points=400):
        if radius > min(width, height)/2: radius = min(width, height)/2
        l_hor = width - 2*radius; l_ver = height - 2*radius
        l_arc = 0.5*np.pi*radius; total_len = 2*(l_hor+l_ver) + 4*l_arc
        t = np.linspace(0, total_len, n_points)
        x, y = [], []
        dx = width/2 - radius; dy = height/2 - radius
        c1, c2 = (dx, dy), (-dx, dy); c3, c4 = (-dx, -dy), (dx, -dy)
        for d in t:
            if d < l_ver: x.append(width/2); y.append(-height/2+radius+d)
            elif d < l_ver+l_arc: theta=(d-l_ver)/radius; x.append(c1[0]+radius*np.cos(theta)); y.append(c1[1]+radius*np.sin(theta))
            elif d < l_ver+l_arc+l_hor: dist=d-(l_ver+l_arc); x.append(width/2-radius-dist); y.append(height/2)
            elif d < l_ver+2*l_arc+l_hor: theta=(d-(l_ver+l_arc+l_hor))/radius+np.pi/2; x.append(c2[0]+radius*np.cos(theta)); y.append(c2[1]+radius*np.sin(theta))
            elif d < 2*l_ver+2*l_arc+l_hor: dist=d-(l_ver+2*l_arc+l_hor); x.append(-width/2); y.append(height/2-radius-dist)
            elif d < 2*l_ver+3*l_arc+l_hor: theta=(d-(2*l_ver+2*l_arc+l_hor))/radius+np.pi; x.append(c3[0]+radius*np.cos(theta)); y.append(c3[1]+radius*np.sin(theta))
            elif d < 2*l_ver+3*l_arc+2*l_hor: dist=d-(2*l_ver+3*l_arc+l_hor); x.append(-width/2+radius+dist); y.append(-height/2)
            else: theta=(d-(2*l_ver+3*l_arc+2*l_hor))/radius+1.5*np.pi; x.append(c4[0]+radius*np.cos(theta)); y.append(c4[1]+radius*np.sin(theta))
        x=np.array(x); y=np.array(y); x[-1], y[-1] = x[0], y[0]
        return x, y

    def calc_impedance(x, y, z):
        base = 2.0 * np.ones_like(x)
        dist_h = (x - (-1.0))**2 + (y - 0.7)**2 
        anom_h = 1.3 * np.exp(-dist_h / 0.2)
        dist_l = (x - 1.0)**2 + (y - (-0.7))**2
        anom_l = -0.9 * np.exp(-dist_l / 0.2)
        return base + anom_h + anom_l + np.random.normal(0, 0.03, size=x.shape)

    n_layers=5; n_passes=3; layer_depth=0.35; step_over=0.25; start_z=0.8
    init_w=3.2; init_h=2.2; init_r=0.6
    all_x, all_y, all_z = [], [], []
    for i in range(n_layers):
        cz = start_z - i*layer_depth
        for j in range(n_passes):
            w = init_w - j*step_over*2; h = init_h - j*step_over*2
            r = max(0.1, init_r - j*step_over*0.5)
            if w<=0 or h<=0: continue
            tx, ty = generate_path(w, h, r, 200)
            tz = np.full_like(tx, cz)
            all_x.append(tx); all_y.append(ty); all_z.append(tz)
    full_x=np.concatenate(all_x); full_y=np.concatenate(all_y); full_z=np.concatenate(all_z)
    impedance = calc_impedance(full_x, full_y, full_z)

    # --- 2. 绘图设置 ---
    # 物理尺寸: 3.5 x 2.2 英寸 (单栏宽度 + 底部留给按钮的空间)
    # dpi=200: 屏幕显示清晰度 (导出时会用 600)
    fig = plt.figure(figsize=(3.5, 2.2), dpi=200)
    
    # 背景全透明
    fig.patch.set_alpha(0.0)
    
    # 调整布局，给底部按钮留 15% 空间
    plt.subplots_adjust(left=0, right=1, top=1, bottom=0.15)
    
    ax = fig.add_subplot(111, projection='3d')
    ax.set_facecolor('none')
    
    # 视角与相机
    ax.view_init(elev=28, azim=-45) 
    ax.set_axis_off()
    ax.dist = 7 # 镜头推近，消除留白

    # 彩色路径
    colors = [(0.0, "#0000FF"), (0.25, "#00FFFF"), (0.4, "#32CD32"), (0.6, "#228B22"), (0.8, "#FFFF00"), (1.0, "#FF0000")]
    cmap = LinearSegmentedColormap.from_list("Traffic", colors)
    pts = np.array([full_x, full_y, full_z]).T.reshape(-1, 1, 3)
    segs = np.concatenate([pts[:-1], pts[1:]], axis=1)
    # 线宽 1.5 (适配小尺寸)
    lc = Line3DCollection(segs, cmap=cmap, norm=plt.Normalize(1.0, 3.2), lw=1.5, alpha=1.0, zorder=10)
    lc.set_array(impedance)
    ax.add_collection(lc)

    # 半透明盒子 (灰色 #CFD8DC)
    bw = init_w+0.3; bh = init_h+0.3
    zt = start_z+0.2; zb = start_z-(n_layers-1)*layer_depth-0.3
    rx, ry = bw/2, bh/2
    verts = np.array([[-rx,-ry,zb],[rx,-ry,zb],[rx,ry,zb],[-rx,ry,zb],[-rx,-ry,zt],[rx,-ry,zt],[rx,ry,zt],[-rx,ry,zt]])
    faces = [[verts[i] for i in [0,1,2,3]], [verts[i] for i in [4,5,6,7]], [verts[i] for i in [0,1,5,4]], 
             [verts[i] for i in [2,3,7,6]], [verts[i] for i in [1,2,6,5]], [verts[i] for i in [0,4,7,3]]]
    
    stock = Poly3DCollection(faces, alpha=0.15, linewidths=0.6, facecolor='#CFD8DC', edgecolor='#78909C', zorder=1)
    ax.add_collection3d(stock)

    # --- 3. 标签 (字号适配) ---
    font_style = dict(fontsize=8, fontweight='bold', zorder=101)
    
    # High Z
    idx_max = np.argmax(impedance)
    hx, hy, hz = full_x[idx_max], full_y[idx_max], full_z[idx_max]
    ax.scatter(hx, hy, hz, color='red', s=30, ec='white', lw=1.0, zorder=100)
    safe_z = zt + 0.35 
    safe_x_left = -rx - 0.2
    ax.plot([hx, hx, safe_x_left], [hy, hy, hy], [hz, safe_z, safe_z], color='#333333', lw=1.0, zorder=100)
    ax.text(safe_x_left - 0.1, hy, safe_z, r"$\mathbf{High\ Z}$", color='#D32F2F', ha='right', va='center', **font_style)

    # Low Z
    idx_min = np.argmin(impedance)
    lx, ly, lz = full_x[idx_min], full_y[idx_min], full_z[idx_min]
    ax.scatter(lx, ly, lz, color='blue', s=30, ec='white', lw=1.0, zorder=100)
    safe_x_right = rx + 0.2
    ax.plot([lx, lx, safe_x_right], [ly, ly, ly], [lz, safe_z, safe_z], color='#333333', lw=1.0, zorder=100)
    ax.text(safe_x_right + 0.1, ly, safe_z, r"$\mathbf{Low\ Z}$", color='#1976D2', ha='left', va='center', **font_style)

    # 极限裁剪
    ax.set_xlim(-rx - 1.0, rx + 1.0) 
    ax.set_ylim(-ry - 0.2, ry + 0.2)
    ax.set_zlim(zb, zt + 0.6)
    ax.set_box_aspect([2, 1, 0.8])
    
    # --- 4. 交互式保存按钮 ---
    # 在底部居中放置按钮
    ax_save = plt.axes([0.3, 0.02, 0.4, 0.08]) # [left, bottom, width, height]
    btn_save = Button(ax_save, 'Save HD (Transparent)', color='#EEEEEE', hovercolor='#B2EBF2')
    
    def save_action(event):
        # 临时隐藏按钮轴，防止按钮被保存进图片
        ax_save.set_visible(False)
        
        timestamp = int(time.time())
        filename_png = f"smif_small_hd_{timestamp}.png"
        filename_pdf = f"smif_small_hd_{timestamp}.pdf"
        
        print(f"Saving {filename_png} (600 DPI)...")
        
        # 核心：dpi=600, transparent=True
        # bbox_inches='tight' 会自动裁剪掉隐藏按钮后的多余空白
        plt.savefig(filename_png, transparent=True, bbox_inches='tight', pad_inches=0, dpi=600)
        plt.savefig(filename_pdf, transparent=True, bbox_inches='tight', pad_inches=0)
        
        # 恢复按钮显示
        ax_save.set_visible(True)
        print("Done!")

    btn_save.on_clicked(save_action)
    
    plt.show()
    return btn_save

if __name__ == "__main__":
    b = generate_smif_small_hd_interactive()