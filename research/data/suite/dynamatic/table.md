| kernel | vectors | Dynamatic cycles per call (simulated; answers = C) | cycles per iteration (simulated, on-merges) | lower bound, any placement | period, ns (ESTIMATE) | ns per iteration (ESTIMATE) | latency per call, ns (ESTIMATE): mean (range) | measured period, ns (routed, 1 seed, 2026-08) |
|---|---|---|---|---|---|---|---|---|
| admm | main() | not simulated (float argument) | - | - | - | - | - | - |
| atax | main() | not simulated (LSQ) | - | - | - | - | - | - |
| atax_float | main() | not simulated (floating point (memref<400xf32>)) | - | - | - | - | - | - |
| bicg | main() | not simulated (LSQ) | - | - | - | - | - | - |
| bicg_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| binary_search | main() | 240 (1 call) | 3.00 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb4 3) | 1 | 8.06 | 24.2 | 1934.8 (1934.8-1934.8; 1 calls) | - |
| branchloop | kernels/branchloop/vec.hex | 2-213 (14 calls) | 3.44 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb3 1) | 1 | 10.70 | 36.8 | 486.1 (21.4-2279.1; 14 calls) | - |
| brhash | kernels/brhash/vec.hex | 2-770 (10 calls) | 3.00 | 1 | 12.13 | 36.4 | 1443.8 (24.3-9342.3; 10 calls) | - |
| cmpchain | kernels/cmpchain/vec.hex | 2-6 (17 calls) | - | - | 7.68 | - (no loop) | 33.9 (15.4-46.1; 17 calls) | - |
| cnn | main() | not simulated (LSQ) | - | - | - | - | - | - |
| collatz | research/data/eventgraph/gate/col18.hex | 2-336 (17 calls) | 1.00 | 1 | 15.48 | 15.5 | 1500.6 (31.0-5201.1; 17 calls) | 14.05 (cycles x period = 14.05) |
| collatz64 | research/data/eventgraph/gate/c6419.hex | 2-951 (18 calls) | 1.00 | 1 | 17.11 | 17.1 | 3963.4 (34.2-16273.6; 18 calls) | 17.84 (cycles x period = 17.84) |
| cordic | main() | not simulated (float argument) | - | - | - | - | - | - |
| countloop | kernels/countloop/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 8.36 | 8.4 | 341.1 (16.7-2157.2; 10 calls) | - |
| covariance | main() | not simulated (LSQ) | - | - | - | - | - | - |
| covariance_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| digitdiv | main() | 362 (1 call) | 39.50 | 35 | 7.69 | 303.8 | 2784.0 (2784.0-2784.0; 1 calls) | - |
| divergent_paths | main() | not simulated (LSQ) | - | - | - | - | - | - |
| dot2 | kernels/dot2/vec.hex | 3-194 (8 calls) | 5.98 | 1 | 9.92 | 59.3 | 1212.2 (29.7-1923.6; 8 calls) | - |
| factorial | research/data/suite/vec/factorial.hex | 3-55 (12 calls) | 13.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb3 13) | 4 | 9.98 | 129.8 | 233.8 (30.0-549.1; 12 calls) | - |
| fill | kernels/fill/vec.hex | 3-43 (5 calls) | 1.00 | 1 | 10.95 | 11.0 | 208.1 (32.9-470.9; 5 calls) | - |
| fir | research/data/suite/vec/fir.hex | 6002 (2 calls) | 5.99 | 1 | 8.12 | 48.7 | 48738.0 (48738.0-48738.0; 2 calls) | - |
| fixed | main() | not simulated (float argument) | - | - | - | - | - | - |
| float_basic | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| fold64 | kernels/fold64/vec.hex | 2-257 (10 calls) | 1.00 | 1 | 11.93 | 11.9 | 448.7 (23.9-3067.2; 10 calls) | - |
| gather | kernels/gather/vec.hex | 3-226 (9 calls) | 6.98 | 1 | 9.92 | 69.2 | 1510.5 (29.7-2240.9; 9 calls) | - |
| gaussian | main() | not simulated (LSQ) | - | - | - | - | - | - |
| gcd | research/data/eventgraph/gate/gcd18.hex | 2-163 (18 calls) | 0.99 (bb11, the most executed of 5 loops; median back-edge interval of the others: bb3 1, bb5 1, bb7 1, bb10 4) | 1 | 12.55 | 12.4 | 430.0 (25.1-1669.7; 8 calls, research/data/suite/vec/gcd8.hex) | - |
| gemm | main() | not simulated (floating point (sitofp)) | - | - | - | - | - | - |
| gemm_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| gemver | main() | not simulated (LSQ) | - | - | - | - | - | - |
| gemver_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| gesummv_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| get_tanh | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| gsum | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| gsumif | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| histogram | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| horner | kernels/horner/vec.hex | 2-1282 (11 calls) | 5.00 | 4 | 8.36 | 41.8 | 1601.6 (16.7-10719.3; 11 calls) | - |
| if_convert | main() | 1125 (1 call) | 6.00 | 4 | 10.95 | 65.7 | 12319.3 (12319.3-12319.3; 1 calls) | - |
| if_loop_1 | research/data/suite/vec/if_loop_1.hex | 3-202 (8 calls) | 1.99 | 1 | 9.99 | 19.9 | 1145.8 (30.0-2017.1; 8 calls) | - |
| if_loop_2 | research/data/suite/vec/if_loop_2.hex | 3-202 (8 calls) | 1.99 | 1 | 8.36 | 16.7 | 1064.0 (25.1-1689.0; 8 calls) | - |
| if_loop_3 | main() | 303 (1 call) | 3.00 | 1 | 9.18 | 27.5 | 2780.5 (2780.5-2780.5; 1 calls) | - |
| if_loop_add | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| if_loop_mul | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| iir | main() | 5996 (1 call) | 5.99 | 4 | 8.12 | 48.7 | 48689.3 (48689.3-48689.3; 1 calls) | - |
| image_resize | main() | 1833 (1 call) | 1.97 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 61) | 1 | 9.64 | 18.9 | 17671.0 (17671.0-17671.0; 1 calls) | - |
| insertion_sort | main() | not simulated (LSQ) | - | - | - | - | - | - |
| ipow | research/data/eventgraph/gate/ipow17.hex | 2-157 (17 calls) | 5.00 | 4 | 10.00 | 50.0 | 513.9 (20.0-1569.3; 17 calls) | - |
| isprime | research/data/alltable/isp17.hex | 2-2139 (18 calls) | 1.00 (bb4, the most executed of 3 loops; median back-edge interval of the others: bb3 22, bb6 1) | 1 | 9.26 | 9.3 | 2501.2 (18.5-19815.3; 18 calls) | - |
| iterative_division | research/data/suite/vec/iterative_division.hex | 2-260 (15 calls) | 1.00 | 1 | 10.22 | 10.2 | 754.1 (20.4-2656.8; 15 calls) | - |
| iterative_sqrt | research/data/suite/vec/iterative_sqrt.hex | 2-172 (12 calls) | 9.98 | 8 | 11.11 | 110.8 | 758.2 (22.2-1910.8; 12 calls) | - |
| jacobi_1d_imper | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_2mm | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_2mm_float | main() | not simulated (float argument) | - | - | - | - | - | - |
| kernel_3mm | main() | not simulated (LSQ) | - | - | - | - | - | - |
| kernel_3mm_float | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| kmp | main() | not simulated (LSQ) | - | - | - | - | - | - |
| lfsrfind | kernels/lfsrfind/vec.hex | 3-514 (10 calls) | 2.00 | 1 | 9.74 | 19.5 | 901.1 (29.2-5007.0; 10 calls) | - |
| loop_array | main() | not simulated (LSQ) | - | - | - | - | - | - |
| loop_path | main() | 337 (1 call) | 2.00 | 1 | 16.13 | 32.3 | 5436.7 (5436.7-5436.7; 1 calls) | - |
| lu | main() | not simulated (floating point (memref<9xf32>)) | - | - | - | - | - | - |
| matching | main() | not simulated (LSQ) | - | - | - | - | - | - |
| matching_2 | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| matrix | main() | 162005 (1 call) | 5.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 5400, bb2 180) | 1 | 9.64 | 57.2 | 1561805.2 (1561805.2-1561805.2; 1 calls) | - |
| matrix_power | main() | not simulated (LSQ) | - | - | - | - | - | - |
| matvec | main() | 60004 (1 call) | 5.98 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 600) | 1 | 8.14 | 48.7 | 488487.5 (488487.5-488487.5; 1 calls) | - |
| memsum | kernels/memsum/vec.hex | 3-194 (5 calls) | 5.98 | 1 | 9.92 | 59.3 | 1033.2 (29.7-1923.6; 5 calls) | - |
| mul_example | main() | 1002 (1 call) | 9.91 | 1 | 8.06 | 79.9 | 8077.7 (8077.7-8077.7; 1 calls) | - |
| mvt_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| nest3 | kernels/nest3/vec.hex | 2-242 (12 calls) | 1.00 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 11, bb2 3) | 1 | 11.06 | 11.1 | 545.6 (22.1-2676.5; 12 calls) | - |
| nested | kernels/nested/vec.hex | 2-290 (11 calls) | 1.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 8) | 1 | 9.98 | 10.0 | 416.5 (20.0-2894.9; 11 calls) | - |
| nested_conditionals_1 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| nested_conditionals_2 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| nested_loop | main() | 2419 (1 call) | 6.00 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 1208) | 4 | 7.43 | 44.6 | 17964.5 (17964.5-17964.5; 1 calls) | - |
| path_profiling | main() | not simulated (LSQ) | - | - | - | - | - | - |
| pivot | main() | not simulated (LSQ) | - | - | - | - | - | - |
| polyn_mult | main() | not simulated (LSQ) | - | - | - | - | - | - |
| prediction | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| quadrec | kernels/quadrec/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 9.09 | 9.1 | 352.8 (18.2-2345.7; 10 calls) | - |
| share_test_1 | main() | 11997 (1 call) | 5.99 (bb1, the most executed of 2 loops; median back-edge interval of the others: bb2 6) | 1 | 9.74 | 58.4 | 116884.0 (116884.0-116884.0; 1 calls) | - |
| share_test_2 | main() | 902 (1 call) | 8.92 | 1 | 10.30 | 91.9 | 9293.0 (9293.0-9293.0; 1 calls) | - |
| simple_example_1 | main() | 2 (1 call) | - | - | 2.38 | - (no loop) | 4.8 (4.8-4.8; 1 calls) | - |
| single_loop | main() | 3009 (1 call) | 6.00 | 4 | 6.72 | 40.3 | 20222.5 (20222.5-20222.5; 1 calls) | - |
| sobel | main() | 11329 (1 call) | 4.67 (bb7, the most executed of 4 loops; median back-edge interval of the others: bb1 755, bb2 57, bb6 17) | 1 | 9.29 | 43.4 | 105282.0 (105282.0-105282.0; 1 calls) | - |
| sparse | main() | not simulated (floating point (memref<100xf32>)) | - | - | - | - | - | - |
| spmv | main() | 150 (1 call) | 5.15 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 7) | 1 | 8.36 | 43.1 | 1254.2 (1254.2-1254.2; 1 calls) | - |
| sqrtsub | kernels/sqrtsub/vec.hex | 2-258 (13 calls) | 1.00 | 1 | 8.36 | 8.4 | 292.0 (16.7-2157.2; 13 calls) | - |
| stencil_2d | main() | 1518 (1 call) | 4.66 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 54, bb2 17) | 1 | 8.68 | 40.4 | 13169.3 (13169.3-13169.3; 1 calls) | - |
| straight | kernels/straight/vec.hex | 1 (12 calls) | - | - | 14.92 | - (no loop) | 14.9 (14.9-14.9; 12 calls) | - |
| subdiag | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| subdiag_fast | main() | not simulated (floating point (memref<1000xf32>)) | - | - | - | - | - | - |
| sum3 | main() | 12 (1 call) | 1.00 | 1 | 8.36 | 8.4 | 100.3 (100.3-100.3; 1 calls) | - |
| sumi3_mem | research/data/suite/vec/sumi3_mem.hex | 10002 (3 calls) | 9.99 | 1 | 8.85 | 88.4 | 88540.1 (88540.1-88540.1; 3 calls) | - |
| symm_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| syr2k_float | main() | not simulated (floating point (memref<900xf32>)) | - | - | - | - | - | - |
| test_bitint | research/data/suite/vec/test_bitint.hex | 62 (6 calls) | 5.44 | 1 | 8.14 | 44.3 | 504.7 (504.7-504.7; 6 calls) | - |
| test_bool_array | main() | 3 (1 call) | - | - | 3.56 | - (no loop) | 10.7 (10.7-10.7; 1 calls) | - |
| test_constant_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| test_divui | main() | 36 (1 call) | - | - | - (no arc in the model) | - (no loop) | - | - |
| test_double | main() | not simulated (type <f64>) | - | - | - | - | - | - |
| test_flatten_array | main() | 1067 (1 call) | 1.93 (bb3, the most executed of 3 loops; median back-edge interval of the others: bb1 266, bb2 33) | 1 | 8.14 | 15.7 | 8686.4 (8686.4-8686.4; 1 calls) | - |
| test_fneg | main() | not simulated (float argument) | - | - | - | - | - | - |
| test_int16 | research/data/suite/vec/test_int16.hex | 1 (1 call) | - | - | - (no arc in the model) | - (no loop) | - | - |
| test_internal_array | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| test_loop_free | research/data/suite/vec/test_loop_free.hex | 3 (10 calls) | - | - | 3.85 | - (no loop) | 11.6 (11.6-11.6; 10 calls) | - |
| test_memory_1 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | 83.6 (83.6-83.6; 1 calls) | - |
| test_memory_10 | main() | 11 (1 call) | 2.00 | 1 | 8.36 | 16.7 | 92.0 (92.0-92.0; 1 calls) | - |
| test_memory_11 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_12 | main() | 13 (1 call) | 2.33 | 1 | 7.71 | 18.0 | 100.2 (100.2-100.2; 1 calls) | - |
| test_memory_13 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_14 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_15 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_16 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_17 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_18 | main() | 20 (1 call) | 3.50 | 1 | 7.79 | 27.3 | 155.7 (155.7-155.7; 1 calls) | - |
| test_memory_2 | main() | 10 (1 call) | 1.67 | 1 | 8.36 | 13.9 | 83.6 (83.6-83.6; 1 calls) | - |
| test_memory_3 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_4 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_5 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_6 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_7 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_8 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_memory_9 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_smallbound | main() | not simulated (LSQ) | - | - | - | - | - | - |
| test_stdint | main() | 1002 (1 call) | 9.91 | 1 | 8.14 | 80.7 | 8157.2 (8157.2-8157.2; 1 calls) | - |
| test_unroll | main() | not simulated (internal array (handshake.ram)) | - | - | - | - | - | - |
| threshold | main() | not simulated (LSQ) | - | - | - | - | - | - |
| triangular | main() | not simulated (LSQ) | - | - | - | - | - | - |
| trisolv | main() | not simulated (LSQ) | - | - | - | - | - | - |
| twoloops | kernels/twoloops/vec.hex | 3-258 (11 calls) | 1.00 (bb3, the most executed of 2 loops; median back-edge interval of the others: bb1 1) | 1 | 9.09 | 9.1 | 514.1 (27.3-2345.7; 11 calls) | - |
| unused_arg | research/data/suite/vec/unused_arg.hex | 2 (6 calls) | - | - | 0.97 | - (no loop) | 1.9 (1.9-1.9; 6 calls) | - |
| varshift | kernels/varshift/vec.hex | 2-258 (10 calls) | 1.00 | 1 | 11.84 | 11.8 | 493.6 (23.7-3054.2; 10 calls) | - |
| vector_rescale | main() | 6002 (1 call) | 5.99 | 1 | 8.12 | 48.7 | 48738.0 (48738.0-48738.0; 1 calls) | - |
| video_filter | main() | 5403 (1 call) | 5.93 (bb2, the most executed of 2 loops; median back-edge interval of the others: bb1 180) | 1 | 9.64 | 57.1 | 52087.5 (52087.5-52087.5; 1 calls) | - |
| while_loop_1 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| while_loop_2 | main() | not simulated (LSQ) | - | - | - | - | - | - |
| while_loop_3 | main() | 13 (1 call) | 5.00 | 4 | 6.80 | 34.0 | 88.4 (88.4-88.4; 1 calls) | - |
| wrap_if | main() | not simulated (LSQ) | - | - | - | - | - | - |
| xorshift | research/data/eventgraph/gate/xor19.hex | 2-1002 (19 calls) | 1.00 | 1 | 11.92 | 11.9 | 1177.4 (23.8-11942.6; 19 calls) | 12.73 (cycles x period = 12.73) |
