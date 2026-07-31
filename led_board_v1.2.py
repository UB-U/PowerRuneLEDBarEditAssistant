import math
import json
import sys
import tkinter as tk
from collections import Counter, defaultdict
import tkinter.messagebox as mb

# ============================================================
# 基本信息初始化
# ============================================================
# 灯板参数
RINGS_LEDNUM = [4, 8, 16, 20, 28, 36, 40, 48, 52, 60]
LEDNUMSUM = sum(RINGS_LEDNUM)          # 312
RINGNUM = len(RINGS_LEDNUM)           # 10
RING_RADIUS = [25, 55, 90, 125, 160, 195, 230, 265, 300, 335] 

BG_COLOR = '#c8d4dc'
CANVAS_BG = '#d0d8e0'

History_Buffer= [set()]#数据缓存区
data_idx=current_idx=0

'''生成LED
    格式：
    index:编号 
    x坐标 
    y坐标
    环数
    角度
    '''
def LedLayout_Init():
    leds = []
    idx = 0
    for ring_i, cnt in enumerate(RINGS_LEDNUM):
        radius = RING_RADIUS[ring_i]
        angle_step = 360.0 / cnt #间隔角度
        base_angle = 90.0  # 起始角度
        for pos in range(cnt):
            angle_deg = base_angle + pos * angle_step
            angle_rad = math.radians(angle_deg)
            leds.append({
                'index': idx,
                'x': round(radius * math.cos(angle_rad), 2),
                'y': round(radius * math.sin(angle_rad), 2),
                'ring': ring_i,
                'angle_deg': round(angle_deg % 360, 1), 
            })
            idx += 1
    return leds


LED_DATA = LedLayout_Init()
assert len(LED_DATA) == LEDNUMSUM
LED_MAP = {led['index']: led for led in LED_DATA}
RING_STEP = [360.0 / c for c in RINGS_LEDNUM]
RING_START = [sum(RINGS_LEDNUM[:i]) for i in range(RINGNUM)]

# 环判定边界 
RING_BOUNDS = [0.0]  # RING_BOUNDS[i] : 环i的下界
for i in range(RINGNUM - 1):
    RING_BOUNDS.append((RING_RADIUS[i] + RING_RADIUS[i+1]) / 2)
last_gap = RING_RADIUS[-1] - RING_RADIUS[-2]
RING_BOUNDS.append(RING_RADIUS[-1] + last_gap / 2)

# ============================================================
# 编码器
# ============================================================
def encode_continuous(on_indices):
    if not on_indices:
        return []
    sorted_on = sorted(set(int(x) for x in on_indices))
    for v in sorted_on:
        if v < 0 or v >= LEDNUMSUM:
            raise ValueError(f"LED编号溢出: {v}")

    #数组书写
    segments = []
    start = prev = sorted_on[0]
    cnt = 1
    for val in sorted_on[1:]:
        if val == prev + 1:
            cnt += 1
        else:
            segments.append({'start': start, 'cnt': cnt})
            start = prev = val
            cnt = 1
        prev = val
    segments.append({'start': start, 'cnt': cnt})

    if (len(segments) >= 2
            and segments[0]['start'] == 0
            and segments[-1]['start'] + segments[-1]['cnt'] - 1 == LEDNUMSUM - 1):
        merged = {
            'start': segments[-1]['start'],
            'cnt': segments[-1]['cnt'] + segments[0]['cnt'],
        }
        segments = [merged] + segments[1:-1]
    return segments


def decode_continuous(segments):
    result = set()
    for seg in segments:
        for i in range(seg['cnt']):
            result.add((seg['start'] + i) % LEDNUMSUM)#支持首尾连接
    return sorted(result)


def arr_Output(on_indices):
    segs = encode_continuous(on_indices)
    body = ", ".join(f"{{{s['start']}, {s['cnt']}}}" for s in segs)
    return (f"共{len(segs)}段  \n"
            f"uint8_t seg_count = {len(segs)};\n"
            f"uint16_t led_seg[{len(segs)}][2] = {{{body}}};")



def layout_json_Output(path="led_layout.json"):
    data = {
        'total_leds': LEDNUMSUM, 'rings': RINGS_LEDNUM,
        'ring_radius': RING_RADIUS, 'spiral_offset_deg': 0,
        'description': f'至LED{LEDNUMSUM-1}',
        'leds': LED_DATA,
    }
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    return path


# ============================================================
# GUI
# ============================================================
class LEDBoardGUI:
    #窗口大小
    CANVAS_SIZE = 850
    CENTER = CANVAS_SIZE // 2
    BOARD_R = RING_RADIUS[-1] + 28

    LED_SIZE = 13
    LED_HALF = LED_SIZE / 2

    # 空间哈希参数
    CELL = 20  # 哈希格子大小(像素)
    HASH_W = CANVAS_SIZE // CELL + 2
    HASH_H = CANVAS_SIZE // CELL + 2

    # 颜色
    COL_OFF  = '#3a4a5a'
    COL_ON   = '#00dd77'
    COL_EDGE_OFF  = '#5a6a7a'
    COL_EDGE_ON   = '#00ffaa'

    DEAWDELAY = 50

    def __init__(self, root):
        #窗口框架初始化
        self.root = root
        self.root.title("312灯灯板模拟器 ")
        self.root.geometry("1000x950")
        self.root.configure(bg=BG_COLOR)

        #灯带状态初始化
        self.on_leds = set()
        self.rect_ids = [None] * LEDNUMSUM
        self._last_encode_time = 0
        self._pending_encode = False
        self.drag_state = None          # None | 'add' | 'remove'
        self.dragged_leds = set()
        self._encode_job = None

        # 空间哈希表: (cell_x, cell_y) → [led_index, ...]
        self._hash_grid = defaultdict(list)
        # 记录每个LED的画布坐标, 供距离计算用
        self._canvas_pos = [(0.0, 0.0)] * LEDNUMSUM

        self._build()
        self._build_hash()
        self._draw_all()
        self._update_info()



    # ---------- UI框架 ----------
    def _build(self):
        bar = tk.Frame(self.root, bg=BG_COLOR)
        bar.pack(side=tk.TOP, fill=tk.X, padx=8, pady=5)
        self.info_var = tk.StringVar(value="")
        tk.Label(bar, textvariable=self.info_var, font=("Arial", 11, "bold"),
                 fg="#223344", bg=BG_COLOR).pack(side=tk.LEFT)
        for text, cmd in [("撤销(Ctrl+z)",self._undo),("重做(Ctrl+y)",self._redo),
            ("全选", self._select_all), ("清空(右键)", self._clear_all),
            ("外圈60", self._demo_outer), ("内圈12", self._demo_inner),
             ("编码输出▼", self._show_output),
        ]:
            tk.Button(bar, text=text, command=cmd, width=8,
                      bg='#3a5a7a', fg='white', activebackground='#5a7a9a',
                      relief=tk.FLAT, font=("Arial", 9)).pack(side=tk.LEFT, padx=3)

        self.canvas = tk.Canvas(self.root, width=self.CANVAS_SIZE,
                                height=self.CANVAS_SIZE, bg=CANVAS_BG,
                                highlightthickness=1, highlightbackground='#8899aa')
        self.canvas.pack(padx=5, pady=5)
        #键鼠功能绑定
        self.canvas.bind("<Button-1>", self._on_click)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<Button-3>", lambda e: self._clear_all())
        self.root.bind("<Control-z>", lambda e: self._undo())
        self.root.bind("<Control-y>", lambda e: self._redo())   

        self.output = tk.Text(self.root, height=8, font=("Consolas", 10),
                              bg='#0d1117', fg='#00ff88', insertbackground='white')
        self.output.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=3)

    # ---------- 坐标转换 ----------
    def _world_to_canvas(self, wx, wy):
        return self.CENTER + wx, self.CENTER - wy

    # ----------  空间哈希索引构建 ----------
    def _build_hash(self):
        self._hash_grid.clear()
        for led in LED_DATA:
            cx, cy = self._world_to_canvas(led['x'], led['y'])
            self._canvas_pos[led['index']] = (cx, cy)
            
            x0 = int((cx - self.LED_HALF) // self.CELL)
            y0 = int((cy - self.LED_HALF) // self.CELL)
            x1 = int((cx + self.LED_HALF) // self.CELL)
            y1 = int((cy + self.LED_HALF) // self.CELL)
            for gx in range(x0, x1 + 1):
                for gy in range(y0, y1 + 1):
                    self._hash_grid[(gx, gy)].append(led['index'])

    def _pick_led(self, x, y):
        gx = int(x // self.CELL)
        gy = int(y // self.CELL)
        # 检查当前桶 + 8邻域
        best = None
        best_d = (self.LED_SIZE * 1.4) ** 2  # 匹配<1.4倍边长
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                bucket = self._hash_grid.get((gx+dx, gy+dy), ())
                for idx in bucket:
                    pcx, pcy = self._canvas_pos[idx]
                    d = (pcx - x)**2 + (pcy - y)**2
                    if d < best_d:
                        best_d = d
                        best = idx
        return best

    def _draw_all(self):
        c = self.CENTER

        # 背景 
        self.canvas.create_oval(c-self.BOARD_R, c-self.BOARD_R,
                                c+self.BOARD_R, c+self.BOARD_R,
                                fill='#b8c8d8', outline='#778899', width=2.5)
        
        # 参考圆
        for r in RING_RADIUS:
            self.canvas.create_oval(c-r, c-r, c+r, c+r,
                                    outline='#99aabb', dash=(4,4), width=1)
        # 径向线
        for deg in range(0, 360, 30):
            rad = math.radians(deg)
            self.canvas.create_line(c, c,
                                     c+self.BOARD_R*math.cos(rad),
                                     c-self.BOARD_R*math.sin(rad),
                                     fill='#aabbcc', width=0.3)
       
        # ---- LED方形图元 ----
        for led in LED_DATA:
            idx = led['index']
            cx, cy = self._canvas_pos[idx]
            rid = self.canvas.create_rectangle(
                cx-self.LED_HALF, cy-self.LED_HALF,
                cx+self.LED_HALF, cy+self.LED_HALF,
                fill=self.COL_OFF, outline=self.COL_EDGE_OFF, width=1,
                tags="led"
            )
            self.rect_ids[idx] = rid
            # 内点
            inner = self.LED_HALF * 0.45
            self.canvas.create_rectangle(
                cx-inner, cy-inner, cx+inner, cy+inner,
                fill='#2a3a4a', outline='', tags="dot"
            )

        # 关键编号标注 
        for ri in range(RINGNUM):
            rl = [l for l in LED_DATA if l['ring'] == ri]
            for led in [rl[0], rl[-1]]:
                cx, cy = self._canvas_pos[led['index']]
                col = '#cc6600' if led['index'] == rl[-1] else '#cc2222'
                self.canvas.create_text(cx, cy+self.LED_HALF+7,
                                        text=str(led['index']), fill=col,
                                        font=("Arial",6, "bold"),
                                        tags="lbl")

        # 图元层级
        self.canvas.tag_raise("dot")
        self.canvas.tag_raise("led")
        self.canvas.tag_raise("lbl")
        self.canvas.tag_raise("mark")
# ============================================================
# 事件
# ============================================================
    def _on_click(self, pos):
        idx = self._pick_led(pos.x, pos.y)
        if idx is None:
            return
        
    def _on_drag(self, pos):
        idx = self._pick_led(pos.x, pos.y)
        if idx is None:
            return

        # 首次拖动确定操作亮/灭
        if self.drag_state is None:
            if idx in self.on_leds:
                self.drag_state = 'remove'
            else:
                self.drag_state = 'add'

        # 拖动过程中，同一LED只处理一次
        if idx in self.dragged_leds:
            return

        self.dragged_leds.add(idx)
        if self.drag_state == 'add' and idx not in self.on_leds:
            self._toggle(idx, schedule=False)
        elif self.drag_state == 'remove' and idx in self.on_leds:
            self._toggle(idx, schedule=False)


    def _on_release(self, pos):
        global History_Buffer,current_idx
        self.drag_state = None
        self.dragged_leds.clear()

        # ===== 历史记录 =====
        # 删除 redo 分支
        if current_idx < len(History_Buffer) - 1:
            History_Buffer = History_Buffer[:current_idx + 1]

        History_Buffer.append(set(self.on_leds))
        current_idx += 1
        # ====================

        self._trigger_encode()#拖动结束后统一编码


    def _toggle(self, idx, schedule=False):#单个LED状态切换
        
        if idx in self.on_leds:
            self.on_leds.discard(idx)
            self.canvas.itemconfig(
                self.rect_ids[idx],
                fill=self.COL_OFF,
                outline=self.COL_EDGE_OFF
            )
        else:
            self.on_leds.add(idx)
            self.canvas.itemconfig(
                self.rect_ids[idx],
                fill=self.COL_ON,
                outline=self.COL_EDGE_ON
            )

        self._update_info()

        if schedule:
            self._trigger_encode()


    def _trigger_encode(self):#消抖触发器
    
        if self._encode_job is not None:
            self.canvas.after_cancel(self._encode_job)
        self._encode_job = self.canvas.after(80, self._schedule_encode)#延时80ms


    def _schedule_encode(self):
        if self._pending_encode: return
        self._pending_encode = True
        self.root.after(self.DEAWDELAY, self._do_encode)


    def _do_encode(self):
        self._pending_encode = False
        segs = encode_continuous(self.on_leds) if self.on_leds else []
        self.info_var.set(
            f"LED总数: {LEDNUMSUM} | 亮: {len(self.on_leds)} | "
            f"段数: {len(segs)} | 拖动连续点灯 "
        )

    def _update_info(self):
        segs = encode_continuous(self.on_leds) if self.on_leds else []
        self.info_var.set(
            f"LED总数: {LEDNUMSUM} | 亮: {len(self.on_leds)} | "
            f"段数: {len(segs)} | 拖动连续点灯 "
        )

    # ---------- 功能键 ----------
    def _clear_all(self):
        if not self.on_leds: return
        for idx in self.on_leds:
            self.canvas.itemconfig(self.rect_ids[idx],
                                   fill=self.COL_OFF, outline=self.COL_EDGE_OFF)
        self.on_leds.clear()
        self._update_info()
        self.output.delete(1.0, tk.END)

    def _select_all(self):
        for idx in range(LEDNUMSUM):
            self.on_leds.add(idx)
            _ = self.canvas.itemconfig(self.rect_ids[idx],  
                                   fill=self.COL_ON, outline=self.COL_EDGE_ON)
        self._update_info()
        self._schedule_encode()

    def _demo_outer(self):#最外圈
        for i in range(252, 312): self._toggle(i)
        

    def _demo_inner(self):#内3圈
        for i in range(12): self._toggle(i)
       
    def _undo(self):
        global current_idx
        if current_idx <= 0:
            self._popup_warn("无法撤回")
            return

        current_idx -= 1
        self.on_leds = set(History_Buffer[current_idx])

        for idx in range(LEDNUMSUM):
            if idx in self.on_leds:
                self.canvas.itemconfig(
                    self.rect_ids[idx],
                    fill=self.COL_ON,
                    outline=self.COL_EDGE_ON
                )
            else:
                self.canvas.itemconfig(
                    self.rect_ids[idx],
                    fill=self.COL_OFF,
                    outline=self.COL_EDGE_OFF
                )

        self._update_info()
        self._schedule_encode()
        

    def _popup_warn(self, msg):
        mb.showwarning("提示", msg, parent=self.root)    

    def _redo(self):
        global current_idx
        if current_idx >= len(History_Buffer) - 1:
            self._popup_warn("无法重做")
            return

        current_idx += 1
        self.on_leds = set(History_Buffer[current_idx])

        for idx in range(LEDNUMSUM):
            if idx in self.on_leds:
                self.canvas.itemconfig(
                    self.rect_ids[idx],
                    fill=self.COL_ON,
                    outline=self.COL_EDGE_ON
                )
            else:
                self.canvas.itemconfig(
                    self.rect_ids[idx],
                    fill=self.COL_OFF,
                    outline=self.COL_EDGE_OFF
                )

        self._update_info()
        self._schedule_encode()
        

    def _show_output(self):
        if hasattr(self, "_output_window"):
            try:
                self._output_window.destroy()
            except Exception:
                pass
            del self._output_window

        win = tk.Toplevel(self.root)
        self._output_window = win
        win.title("亮灯编码结果")
        win.geometry("520x360")
        win.resizable(True, True)
        win.protocol("WM_DELETE_WINDOW", self._close_output_window)

        text = tk.Text(
            win,
            wrap=tk.WORD,
            font=("Consolas", 11),
            bg="#f8f8f8",
            relief=tk.FLAT
        )
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        scrollbar = tk.Scrollbar(text)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        text.config(yscrollcommand=scrollbar.set)
        scrollbar.config(command=text.yview)

        if not self.on_leds:
            text.insert(tk.END, "（无亮灯）\n")
            text.config(state=tk.DISABLED)
            return

        segs = encode_continuous(self.on_leds)
        content = []
        content.append(arr_Output(self.on_leds) + "\n")
        content.append("\n")
        content.append(f"亮灯{len(self.on_leds)}个: {sorted(self.on_leds)}\n")

        text.insert(tk.END, "".join(content))
        text.config(state=tk.DISABLED)

    def _close_output_window(self):
        if hasattr(self, "_output_window"):
            self._output_window.destroy()
            del self._output_window
# ============================================================
# 主程序
# ============================================================
if __name__ == "__main__":
        try:
            import tkinter as tk
            root = tk.Tk()
            app = LEDBoardGUI(root)
            root.mainloop()
        except ImportError:
            print("\ntkinter不可用\n");
        except Exception as e:
            print(f"GUI失败: {e}\n"); 
