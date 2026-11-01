# The target's kernel boundary, as wired (yosys netlist of the target build; untrusted naming)

Generated 2026-11-01 from `gcd_hw_03e82630.json.xz` (top `gcd_hw`, nets of `urig`). A yosys net id is a
logical net; the physical nodes come from the decoder. `'0'` is the constant 0.

## `a_v` (kernel `a_data`): 18 distinct non-constant nets, constant bits [31]

| net | bits |
|---|---|
| 807 | [0] |
| 808 | [1] |
| 809 | [2] |
| 810 | [3] |
| 812 | [4] |
| 813 | [5] |
| 814 | [6, 14] |
| 815 | [7] |
| 816 | [8] |
| 817 | [9] |
| 818 | [10] |
| 819 | [11, 20, 21, 22] |
| 845 | [12, 23, 24, 25, 26, 27, 28, 29, 30] |
| 820 | [13] |
| 821 | [15] |
| 822 | [16] |
| 146 | [17, 18] |
| 823 | [19] |
| 0 | [31] |

## `b_v` (kernel `b_data`): 20 distinct non-constant nets, constant bits [22, 24, 26, 27, 29, 30, 31]

| net | bits |
|---|---|
| 824 | [0] |
| 825 | [1] |
| 826 | [2] |
| 827 | [3] |
| 828 | [4] |
| 829 | [5] |
| 831 | [6] |
| 830 | [7] |
| 806 | [8] |
| 832 | [9] |
| 833 | [10] |
| 834 | [11] |
| 835 | [12] |
| 11 | [13, 20, 21, 23, 25, 28] |
| 836 | [14] |
| 16 | [15] |
| 837 | [16] |
| 846 | [17] |
| 838 | [18] |
| 839 | [19] |
| 0 | [22, 24, 26, 27, 29, 30, 31] |

## Handshake nets

| kernel port | net |
|---|---|
| a_req | [1123] |
| b_req | [1123] |
| start_req | [1123] |
| a_ack | [1207] |
| b_ack | [1208] |
| start_ack | [1213] |
| out0_req | [1210] |
| out0_ack | [1209] |
| p_end_req | [1212] |
| p_end_ack | [1211] |
| rst | [841] |

`a_req = b_req = start_req = env_c` (one net): rig `bd_fork` is `assign req_out = {N{req}}`.
`out0_data`: 32 distinct nets. True
