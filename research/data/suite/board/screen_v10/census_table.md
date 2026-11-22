| kernel | rule E: weakest steer x (both bands) | weakest select gate of any kind | formal B24 xtol (weakest steer by its kappa) |
|---|---|---|---|
| fill | 0.045 (ucond_br8) | 0.045 (bd_steer ucond_br8) | memory (not screened) |
| collatz64 | 0.047 (ucond_br6) | 0.047 (bd_steer ucond_br6) | pulses x=0.08; fail x=0.15: RESULT |
| twoloops | 0.047 (ucond_br18) | 0.047 (bd_steer ucond_br18) | pulses none to 0.25; fail none to 0.25 |
| if_loop_2 | 0.062 (ucond_br5) | 0.054 (bd_mux umux3) | memory (not screened) |
| dot2 | 0.055 (ucond_br8) | 0.055 (bd_steer ucond_br8) | memory (not screened) |
| sqrtsub | 0.057 (ucond_br3) | 0.057 (bd_steer ucond_br3) | pulses x=0.10; fail x=0.10: RESULT |
| lfsrfind | 0.062 (ucond_br5) | 0.062 (bd_steer ucond_br5) | pulses x=0.12; fail x=0.12: RESULT |
| varshift | 0.180 (ucond_br7) | 0.069 (bd_mux umux3) | pulses none to 0.25; fail none to 0.25 |
| nested_loop | 0.076 (ucond_br5) | 0.076 (bd_steer ucond_br5) | memory (not screened) |
| single_loop | 0.083 (ucond_br1) | 0.083 (bd_steer ucond_br1) | memory (not screened) |
| memsum | 0.097 (ucond_br8) | 0.084 (bd_mux umux3) | memory (not screened) |
| test_memory_2 | 0.086 (ucond_br5) | 0.086 (bd_steer ucond_br5) | memory (not screened) |
| fold64 | 0.088 (ucond_br10) | 0.088 (bd_steer ucond_br10) | pulses x=0.20; fail none to 0.25 |
| branchloop | 0.089 (ucond_br7) | 0.089 (bd_steer ucond_br7) | pulses x=0.15; fail x=0.20: RESULT |
| vector_rescale | 0.367 (ucond_br2) | 0.093 (bd_mux umux1) | memory (not screened) |
| quadrec | 0.094 (ucond_br15) | 0.094 (bd_steer ucond_br15) | pulses none to 0.25; fail none to 0.25 |
| horner | 0.097 (ucond_br8) | 0.097 (bd_steer ucond_br8) | pulses x=0.20; fail none to 0.25 |
| if_loop_1 | 0.105 (ucond_br5) | 0.105 (bd_steer ucond_br5) | memory (not screened) |
| collatz | 0.108 (ucond_br3) | 0.108 (bd_steer ucond_br3) | pulses none to 0.25; fail x=0.25: RESULT |
| test_memory_1 | 0.111 (ucond_br6) | 0.111 (bd_steer ucond_br6) | memory (not screened) |
| test_stdint | 0.121 (ucond_br2) | 0.111 (bd_mux umux0) | memory (not screened) |
| xorshift | 0.131 (ucond_br6) | 0.131 (bd_steer ucond_br6) | pulses x=0.25; fail none to 0.25 |
| test_bitint | 0.138 (ucond_br1) | 0.138 (bd_steer ucond_br1) | memory (not screened) |
| brhash | 0.142 (ucond_br11) | 0.142 (bd_steer ucond_br11) | pulses none to 0.25; fail none to 0.25 |
| test_flatten_array | 0.222 (ucond_br6) | 0.147 (bd_mux umux9) | memory (not screened) |
| while_loop_3 | 0.186 (ucond_br4) | 0.157 (bd_mux umux1) | memory (not screened) |
| sumi3_mem | 0.158 (ucond_br3) | 0.158 (bd_steer ucond_br3) | memory (not screened) |
| iterative_sqrt | 0.163 (ucond_br12) | 0.163 (bd_steer ucond_br12) | pulses none to 0.25; fail none to 0.25 |
| gather | 0.165 (ucond_br4) | 0.165 (bd_steer ucond_br4) | memory (not screened) |
| ipow | 0.217 (ucond_br4) | 0.180 (bd_mux umux1) | pulses x=0.15; fail none to 0.25 |
| countloop | 0.183 (ucond_br3) | 0.183 (bd_steer ucond_br3) | pulses none to 0.25; fail none to 0.25 |
| binary_search | 0.184 (ucond_br8) | 0.184 (bd_steer ucond_br8) | memory (not screened) |
| if_convert | 0.188 (ucond_br2) | 0.188 (bd_steer ucond_br2) | memory (not screened) |
| iir | 0.313 (ucond_br2) | 0.189 (bd_mux umux2) | memory (not screened) |
| test_loop_free | 0.223 (ucond_br2) | 0.193 (bd_mux umux0) | memory (not screened) |
| mul_example | 0.320 (ucond_br2) | 0.289 (bd_mux umux0) | memory (not screened) |
| loop_path | 0.307 (ucond_br2) | 0.307 (bd_steer ucond_br2) | memory (not screened) |
| share_test_2 | 0.415 (ucond_br2) | 0.415 (bd_steer ucond_br2) | memory (not screened) |
| divmods | no select gate |  | pulses none to 0.25; fail none to 0.25 |
| divmodu | no select gate |  | pulses none to 0.25; fail x=0.00: RESULT |
| simple_example_1 | no select gate |  | memory (not screened) |
| straight | no select gate |  | pulses none to 0.25; fail none to 0.25 |
| test_bool_array | no select gate |  | memory (not screened) |
| test_divui | no select gate |  | pulses none to 0.25; fail none to 0.25 |
| test_int16 | no select gate |  | test_int16 | draws |  (weakest Traceback (most recent call ) |
| unused_arg | no select gate |  | memory (not screened) |
