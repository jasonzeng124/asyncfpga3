| kernel | vectors | Dynamatic cycles per call (simulated; answers = C) | cycles per iteration (simulated, on-merges) | lower bound, any placement | period, ns (ESTIMATE) | ns per iteration (ESTIMATE) | measured period, ns (routed, 1 seed, 2026-08) |
|---|---|---|---|---|---|---|---|
| admm | main() | not simulated (float argument) | - | - | - | - | - |
| atax | main() | not simulated (LSQ) | - | - | - | - | - |
| atax_float | main() | not simulated (floating point (memref<400xf32>)) | - | - | - | - | - |
| bicg | main() | not simulated (LSQ) | - | - | - | - | - |
| bicg_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| binary_search | main() | 240 (1 call) | 3.00 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb4 3) | 1 | 8.06 | 24.2 | - |
| branchloop | kernels/branchloop/vec.hex | 2-213 (14 calls) | 3.44 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb3 1) | 1 | 10.70 | 36.8 | - |
| brhash | kernels/brhash/vec.hex | 2-770 (10 calls) | 3.00 | 1 | 12.13 | 36.4 | - |
| cmpchain | kernels/cmpchain/vec.hex | 2-6 (17 calls) | - | - | 7.68 | - (no loop) | - |
| cnn | main() | not simulated (LSQ) | - | - | - | - | - |
| collatz | research/data/eventgraph/gate/col18.hex | 2-336 (17 calls) | 1.00 | 1 | 15.48 | 15.5 | 14.05 (cycles x period = 14.05) |
| collatz64 | research/data/eventgraph/gate/c6419.hex | 2-951 (18 calls) | 1.00 | 1 | 17.11 | 17.1 | 17.84 (cycles x period = 17.84) |
| cordic | main() | not simulated (float argument) | - | - | - | - | - |
| countloop | kernels/countloop/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 8.36 | 8.4 | - |
| covariance | main() | not simulated (LSQ) | - | - | - | - | - |
| covariance_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| digitdiv | main() | 362 (1 call) | 39.50 | 35 | 7.69 | 303.8 | - |
| divergent_paths | main() | not simulated (LSQ) | - | - | - | - | - |
| factorial | main() | 393 (1 call) | 12.59 (bb2, the most executed of 2 loops) | 4 | 9.98 | 125.7 | - |
| fir | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | - |
| fixed | main() | not simulated (float argument) | - | - | - | - | - |
| float_basic | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| fold64 | kernels/fold64/vec.hex | 2-257 (10 calls) | 1.00 | 1 | 11.93 | 11.9 | - |
| gaussian | main() | not simulated (LSQ) | - | - | - | - | - |
| gcd | research/data/eventgraph/gate/gcd18.hex | 2-163 (18 calls) | 0.99 (bb11, the most executed of 5 loops; median back-edge interval of the others: bb3 1, bb5 1, bb7 1, bb10 4) | 1 | 12.55 | 12.4 | - |
| gemm | main() | not simulated (floating point (sitofp)) | - | - | - | - | - |
| gemm_float | main() | not simulated (float argument) | - | - | - | - | - |
| gemver | main() | not simulated (LSQ) | - | - | - | - | - |
| gemver_float | main() | not simulated (float argument) | - | - | - | - | - |
| gesummv_float | main() | not simulated (float argument) | - | - | - | - | - |
| get_tanh | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| gsum | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| gsumif | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| histogram | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| horner | kernels/horner/vec.hex | 2-1282 (11 calls) | 5.00 | 4 | 8.36 | 41.8 | - |
| if_convert | main() | 1125 (1 call) | 6.00 | 4 | 10.95 | 65.7 | - |
| if_loop_1 | main() | 202 (1 call) | 1.99 | 1 | 9.99 | 19.9 | - |
| if_loop_2 | main() | 202 (1 call) | 1.99 | 1 | 8.36 | 16.6 | - |
| if_loop_3 | main() | 303 (1 call) | 3.00 | 1 | 9.18 | 27.5 | - |
| if_loop_add | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| if_loop_mul | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| iir | main() | 5996 (1 call) | 5.99 | 4 | 8.12 | 48.7 | - |
| image_resize | main() | 1833 (1 call) | 1.97 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 61) | 1 | 9.64 | 18.9 | - |
| insertion_sort | main() | not simulated (LSQ) | - | - | - | - | - |
| ipow | research/data/eventgraph/gate/ipow17.hex | 2-157 (17 calls) | 5.00 | 4 | 10.00 | 50.0 | - |
| isprime | research/data/alltable/isp17.hex | 2-2139 (18 calls) | 1.00 (bb4, the most executed of 3 loops; median back-edge interval of the others: bb3 22, bb6 1) | 1 | 9.26 | 9.3 | - |
| iterative_division | main() | 5 (1 call) | - | - | 10.22 | - (no loop) | - |
| iterative_sqrt | main() | 72 (1 call) | 10.00 | 8 | 11.11 | 111.1 | - |
| jacobi_1d_imper | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_2mm | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_2mm_float | main() | not simulated (float argument) | - | - | - | - | - |
| kernel_3mm | main() | not simulated (LSQ) | - | - | - | - | - |
| kernel_3mm_float | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| kmp | main() | not simulated (LSQ) | - | - | - | - | - |
| lfsrfind | kernels/lfsrfind/vec.hex | 3-514 (10 calls) | 2.00 | 1 | 9.74 | 19.5 | - |
| loop_array | main() | not simulated (LSQ) | - | - | - | - | - |
| loop_path | main() | 337 (1 call) | 2.00 | 1 | 16.13 | 32.3 | - |
| lu | main() | not simulated (floating point (memref<9xf32>)) | - | - | - | - | - |
| matching | main() | not simulated (LSQ) | - | - | - | - | - |
| matching_2 | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| matrix | main() | 162005 (1 call) | 5.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 5400, bb2 180) | 1 | 9.64 | 57.2 | - |
| matrix_power | main() | not simulated (LSQ) | - | - | - | - | - |
| matvec | main() | 60004 (1 call) | 5.98 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 600) | 1 | 8.14 | 48.7 | - |
| memsum | main() | 122 (1 call) | 5.74 | 1 | 9.92 | 56.9 | - |
| mul_example | main() | 1002 (1 call) | 9.91 | 1 | 8.06 | 79.9 | - |
| mvt_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| nest3 | kernels/nest3/vec.hex | 2-242 (12 calls) | 1.00 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 11, bb2 3) | 1 | 11.06 | 11.1 | - |
| nested | kernels/nested/vec.hex | 2-290 (11 calls) | 1.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 8) | 1 | 9.98 | 10.0 | - |
| nested_conditionals_1 | main() | not simulated (LSQ) | - | - | - | - | - |
| nested_conditionals_2 | main() | not simulated (LSQ) | - | - | - | - | - |
| nested_loop | main() | 2419 (1 call) | 6.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 1208) | 4 | 7.43 | 44.6 | - |
| path_profiling | main() | not simulated (LSQ) | - | - | - | - | - |
| pivot | main() | not simulated (LSQ) | - | - | - | - | - |
| polyn_mult | main() | not simulated (LSQ) | - | - | - | - | - |
| prediction | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| quadrec | kernels/quadrec/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 9.09 | 9.1 | - |
| share_test_1 | main() | 11997 (1 call) | 5.99 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb2 6) | 1 | 9.74 | 58.4 | - |
| share_test_2 | main() | 902 (1 call) | 8.92 | 1 | 10.30 | 91.9 | - |
| simple_example_1 | main() | 2 (1 call) | - | - | 2.38 | - (no loop) | - |
| single_loop | main() | 3009 (1 call) | 6.00 | 4 | 6.72 | 40.3 | - |
| sobel | main() | 11329 (1 call) | 4.67 (bb7, the most executed of 4 loops; median back-edge interval of the others: bb1 755, bb2 57, bb6 17) | 1 | 9.29 | 43.4 | - |
| sparse | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - |
| spmv | main() | 150 (1 call) | 5.15 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 7) | 1 | 8.36 | 43.1 | - |
| sqrtsub | kernels/sqrtsub/vec.hex | 2-258 (13 calls) | 1.00 | 1 | 8.36 | 8.4 | - |
| stencil_2d | main() | 1518 (1 call) | 4.66 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 54, bb2 17) | 1 | 8.68 | 40.4 | - |
| straight | kernels/straight/vec.hex | 1 (12 calls) | - | - | 14.92 | - (no loop) | - |
| subdiag | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| subdiag_fast | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - |
| sumi3_mem | main() | 10002 (1 call) | 9.99 | 1 | 8.85 | 88.4 | - |
| symm_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| syr2k_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - |
| test_bitint | main() | 62 (1 call) | 5.44 | 1 | 8.14 | 44.3 | - |
| test_bool_array | main() | 3 (1 call) | - | - | 3.56 | - (no loop) | - |
| test_constant_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| test_divui | main() | 36 (1 call) | - | - | - (no arc in the model) | - (no loop) | - |
| test_double | main() | not simulated (type <f64>) | - | - | - | - | - |
| test_flatten_array | main() | 1067 (1 call) | 1.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 266, bb2 33) | 1 | 8.14 | 15.7 | - |
| test_fneg | main() | not simulated (float argument) | - | - | - | - | - |
| test_int16 | main() | 1 (1 call) | - | - | - (no arc in the model) | - (no loop) | - |
| test_internal_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| test_loop_free | main() | 3 (1 call) | - | - | 3.85 | - (no loop) | - |
| test_memory_1 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | - |
| test_memory_10 | main() | 11 (1 call) | 2.00 | 1 | 8.36 | 16.7 | - |
| test_memory_11 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_12 | main() | 13 (1 call) | 2.33 | 1 | 7.71 | 18.0 | - |
| test_memory_13 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_14 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_15 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_16 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_17 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_18 | main() | 20 (1 call) | 3.50 | 1 | 7.79 | 27.3 | - |
| test_memory_2 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | - |
| test_memory_3 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_4 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_5 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_6 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_7 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_8 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_memory_9 | main() | not simulated (LSQ) | - | - | - | - | - |
| test_smallbound | main() | not simulated (LSQ) | - | - | - | - | - |
| test_stdint | main() | 1002 (1 call) | 9.91 | 1 | 8.14 | 80.7 | - |
| test_unroll | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - |
| threshold | main() | not simulated (LSQ) | - | - | - | - | - |
| triangular | main() | not simulated (LSQ) | - | - | - | - | - |
| trisolv | main() | not simulated (LSQ) | - | - | - | - | - |
| twoloops | kernels/twoloops/vec.hex | 3-258 (11 calls) | 1.00 (bb3, the most executed of 2 loops; median back-edge interval of the others: bb1 1) | 1 | 9.09 | 9.1 | - |
| unused_arg | main() | 2 (1 call) | - | - | 0.97 | - (no loop) | - |
| varshift | kernels/varshift/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 11.84 | 11.8 | - |
| vector_rescale | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | - |
| video_filter | main() | 5403 (1 call) | 5.93 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 180) | 1 | 9.64 | 57.1 | - |
| while_loop_1 | main() | not simulated (LSQ) | - | - | - | - | - |
| while_loop_2 | main() | not simulated (LSQ) | - | - | - | - | - |
| while_loop_3 | main() | 13 (1 call) | 5.00 | 4 | 6.80 | 34.0 | - |
| wrap_if | main() | not simulated (LSQ) | - | - | - | - | - |
| xorshift | research/data/eventgraph/gate/xor19.hex | 2-1002 (19 calls) | 1.00 | 1 | 11.92 | 11.9 | 12.73 (cycles x period = 12.73) |
