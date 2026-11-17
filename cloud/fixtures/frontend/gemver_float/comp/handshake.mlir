module {
  handshake.func @gemver_float(%arg0: !handshake.channel<f32>, %arg1: !handshake.channel<f32>, %arg2: memref<100xf32>, %arg3: memref<10xf32>, %arg4: memref<10xf32>, %arg5: memref<10xf32>, %arg6: memref<10xf32>, %arg7: memref<10xf32>, %arg8: memref<10xf32>, %arg9: memref<10xf32>, %arg10: memref<10xf32>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, %arg13: !handshake.control<>, %arg14: !handshake.control<>, %arg15: !handshake.control<>, %arg16: !handshake.control<>, %arg17: !handshake.control<>, %arg18: !handshake.control<>, %arg19: !handshake.control<>, %arg20: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "A", "u1", "v1", "u2", "v2", "w", "x", "y", "z", "A_start", "u1_start", "v1_start", "u2_start", "v2_start", "w_start", "x_start", "y_start", "z_start", "start"], resNames = ["A_end", "u1_end", "v1_end", "u2_end", "v2_end", "w_end", "x_end", "y_end", "z_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg10 : memref<10xf32>] %arg19 (%addressResult_96) %result_140 {connectedBlocks = [7 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg9 : memref<10xf32>] %arg18 (%addressResult_62) %result_140 {connectedBlocks = [5 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0:4 = lsq[%arg8 : memref<10xf32>] (%arg17, %result_54, %addressResult_56, %result_78, %addressResult_80, %dataResult_81, %result_92, %addressResult_94, %addressResult_98, %dataResult_99, %result_112, %addressResult_116, %result_140)  {groupSizes = [1 : i32, 1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs_2, %memEnd_3 = mem_controller[%arg7 : memref<10xf32>] %arg16 (%addressResult_110, %183, %addressResult_132, %dataResult_133) %result_140 {connectedBlocks = [8 : i32, 10 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %outputs_4, %memEnd_5 = mem_controller[%arg6 : memref<10xf32>] %arg15 (%addressResult_22) %result_140 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_6, %memEnd_7 = mem_controller[%arg5 : memref<10xf32>] %arg14 (%addressResult_20) %result_140 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_8, %memEnd_9 = mem_controller[%arg4 : memref<10xf32>] %arg13 (%addressResult_18) %result_140 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_10, %memEnd_11 = mem_controller[%arg3 : memref<10xf32>] %arg12 (%addressResult_16) %result_140 {connectedBlocks = [2 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_12:2, %memEnd_13 = mem_controller[%arg2 : memref<100xf32>] %arg11 (%24, %addressResult, %1#2, %1#3, %1#4) %result_140 {connectedBlocks = [2 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %1:5 = lsq[MC] (%result_14, %addressResult_24, %dataResult_25, %result_58, %addressResult_60, %result_112, %addressResult_114, %outputs_12#1)  {groupSizes = [1 : i32, 1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>)
    %2 = constant %arg20 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %4 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <f32>
    %6 = br %arg20 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <>
    %7 = mux %index [%3, %trueResult_44] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%4, %trueResult_46] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %9 = mux %index [%5, %trueResult_48] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%6, %trueResult_50]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %11 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %13 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %14 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %15 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %16 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %17 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <f32>
    %18 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i32>
    %19 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %20 = br %12 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i64>
    %21 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <i64>
    %22 = br %14 {handshake.bb = 1 : ui32, handshake.name = "br15"} : <i64>
    %23 = br %result {handshake.bb = 1 : ui32, handshake.name = "br16"} : <>
    %24 = constant %result_14 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %25 = mux %index_15 [%15, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_15 [%16, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %27 = mux %index_15 [%17, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %28 = mux %index_15 [%18, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %index_15 [%19, %trueResult_32] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %30 = mux %index_15 [%20, %trueResult_34] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %31 = mux %index_15 [%21, %trueResult_36] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %32 = mux %index_15 [%22, %trueResult_38] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %result_14, %index_15 = control_merge [%23, %trueResult_40]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %33 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %34 = constant %33 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 10 : i32} : <>, <i32>
    %35 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %36 = constant %35 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %38 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3 : i64} : <>, <i64>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i64} : <>, <i64>
    %41 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %42 = shli %29, %40 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %43 = shli %29, %38 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %44 = addi %42, %43 {handshake.bb = 2 : ui32, handshake.name = "addi11"} : <i64>
    %45 = addi %44, %41 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %46 = trunci %45 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%46] %outputs_12#0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %47 = trunci %30 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = load[%47] %outputs_10 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %48 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = load[%49] %outputs_8 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %50 = mulf %dataResult_17, %dataResult_19 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %51 = addf %dataResult, %50 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %52 = trunci %31 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_20, %dataResult_21 = load[%52] %outputs_6 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %53 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %54 = trunci %53 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_22, %dataResult_23 = load[%54] %outputs_4 {handshake.bb = 2 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %55 = mulf %dataResult_21, %dataResult_23 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %56 = addf %51, %55 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %57 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %58 = shli %32, %40 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %59 = shli %32, %38 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %60 = addi %58, %59 {handshake.bb = 2 : ui32, handshake.name = "addi12"} : <i64>
    %61 = addi %60, %57 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %62 = trunci %61 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = store[%62] %56 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <f32>, <i32>, <f32>
    %63 = addi %25, %36 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %64 = cmpi ult, %63, %34 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %64, %63 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %64, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_28, %falseResult_29 = cond_br %64, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_30, %falseResult_31 = cond_br %64, %28 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %64, %29 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i64>
    %trueResult_34, %falseResult_35 = cond_br %64, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i64>
    %trueResult_36, %falseResult_37 = cond_br %64, %31 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_38, %falseResult_39 = cond_br %64, %32 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_40, %falseResult_41 = cond_br %64, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %65 = merge %falseResult_27 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %66 = merge %falseResult_29 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <f32>
    %67 = merge %falseResult_31 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %result_42, %index_43 = control_merge [%falseResult_41]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %68 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %69 = constant %68 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 10 : i32} : <>, <i32>
    %70 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %71 = constant %70 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %72 = constant %result_42 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %73 = addi %67, %71 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %74 = cmpi ult, %73, %69 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %74, %73 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_46, %falseResult_47 = cond_br %74, %65 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <f32>
    %trueResult_48, %falseResult_49 = cond_br %74, %66 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_50, %falseResult_51 = cond_br %74, %result_42 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %trueResult_52, %falseResult_53 = cond_br %74, %72 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %75 = mux %index_55 [%falseResult_53, %trueResult_82] {handshake.bb = 4 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %76 = mux %index_55 [%falseResult_47, %trueResult_84] {handshake.bb = 4 : ui32, handshake.name = "mux12"} : <i1>, [<f32>, <f32>] to <f32>
    %77 = mux %index_55 [%falseResult_49, %trueResult_86] {handshake.bb = 4 : ui32, handshake.name = "mux13"} : <i1>, [<f32>, <f32>] to <f32>
    %result_54, %index_55 = control_merge [%falseResult_51, %trueResult_88]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %78 = constant %result_54 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 0 : i32} : <>, <i32>
    %79 = extui %75 {handshake.bb = 4 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %80 = trunci %79 {handshake.bb = 4 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_56, %dataResult_57 = load[%80] %0#0 {handshake.bb = 4 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %81 = extui %75 {handshake.bb = 4 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %82 = br %dataResult_57 {handshake.bb = 4 : ui32, handshake.name = "br17"} : <f32>
    %83 = br %78 {handshake.bb = 4 : ui32, handshake.name = "br18"} : <i32>
    %84 = br %76 {handshake.bb = 4 : ui32, handshake.name = "br19"} : <f32>
    %85 = br %77 {handshake.bb = 4 : ui32, handshake.name = "br20"} : <f32>
    %86 = br %75 {handshake.bb = 4 : ui32, handshake.name = "br21"} : <i32>
    %87 = br %81 {handshake.bb = 4 : ui32, handshake.name = "br22"} : <i64>
    %88 = br %result_54 {handshake.bb = 4 : ui32, handshake.name = "br23"} : <>
    %89 = mux %index_59 [%82, %trueResult_64] {handshake.bb = 5 : ui32, handshake.name = "mux14"} : <i1>, [<f32>, <f32>] to <f32>
    %90 = mux %index_59 [%83, %trueResult_66] {handshake.bb = 5 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %91 = mux %index_59 [%84, %trueResult_68] {handshake.bb = 5 : ui32, handshake.name = "mux16"} : <i1>, [<f32>, <f32>] to <f32>
    %92 = mux %index_59 [%85, %trueResult_70] {handshake.bb = 5 : ui32, handshake.name = "mux17"} : <i1>, [<f32>, <f32>] to <f32>
    %93 = mux %index_59 [%86, %trueResult_72] {handshake.bb = 5 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %94 = mux %index_59 [%87, %trueResult_74] {handshake.bb = 5 : ui32, handshake.name = "mux19"} : <i1>, [<i64>, <i64>] to <i64>
    %result_58, %index_59 = control_merge [%88, %trueResult_76]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %95 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %96 = constant %95 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 10 : i32} : <>, <i32>
    %97 = source {handshake.bb = 5 : ui32, handshake.name = "source7"} : <>
    %98 = constant %97 {handshake.bb = 5 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %99 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %100 = constant %99 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 3 : i64} : <>, <i64>
    %101 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %102 = constant %101 {handshake.bb = 5 : ui32, handshake.name = "constant18", value = 1 : i64} : <>, <i64>
    %103 = extui %90 {handshake.bb = 5 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %104 = shli %103, %102 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %105 = shli %103, %100 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %106 = addi %104, %105 {handshake.bb = 5 : ui32, handshake.name = "addi13"} : <i64>
    %107 = addi %106, %94 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i64>
    %108 = trunci %107 {handshake.bb = 5 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_60, %dataResult_61 = load[%108] %1#0 {handshake.bb = 5 : ui32, handshake.name = "load7"} : <i32>, <f32>, <i32>, <f32>
    %109 = mulf %dataResult_61, %92 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "mulf2"} : <f32>
    %110 = extui %90 {handshake.bb = 5 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %111 = trunci %110 {handshake.bb = 5 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_62, %dataResult_63 = load[%111] %outputs_0 {handshake.bb = 5 : ui32, handshake.name = "load8"} : <i32>, <f32>, <i32>, <f32>
    %112 = mulf %109, %dataResult_63 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "mulf3"} : <f32>
    %113 = addf %89, %112 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "addf2"} : <f32>
    %114 = addi %90, %98 {handshake.bb = 5 : ui32, handshake.name = "addi5"} : <i32>
    %115 = cmpi ult, %114, %96 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_64, %falseResult_65 = cond_br %115, %113 {handshake.bb = 5 : ui32, handshake.name = "cond_br21"} : <i1>, <f32>
    %trueResult_66, %falseResult_67 = cond_br %115, %114 {handshake.bb = 5 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_68, %falseResult_69 = cond_br %115, %91 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <f32>
    %trueResult_70, %falseResult_71 = cond_br %115, %92 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <f32>
    %trueResult_72, %falseResult_73 = cond_br %115, %93 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %115, %94 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <i64>
    %trueResult_76, %falseResult_77 = cond_br %115, %result_58 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <>
    %116 = merge %falseResult_65 {handshake.bb = 6 : ui32, handshake.name = "merge3"} : <f32>
    %117 = merge %falseResult_69 {handshake.bb = 6 : ui32, handshake.name = "merge4"} : <f32>
    %118 = merge %falseResult_71 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <f32>
    %119 = merge %falseResult_73 {handshake.bb = 6 : ui32, handshake.name = "merge6"} : <i32>
    %result_78, %index_79 = control_merge [%falseResult_77]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %120 = source {handshake.bb = 6 : ui32, handshake.name = "source10"} : <>
    %121 = constant %120 {handshake.bb = 6 : ui32, handshake.name = "constant19", value = 10 : i32} : <>, <i32>
    %122 = source {handshake.bb = 6 : ui32, handshake.name = "source11"} : <>
    %123 = constant %122 {handshake.bb = 6 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %124 = constant %result_78 {handshake.bb = 6 : ui32, handshake.name = "constant21", value = 0 : i32} : <>, <i32>
    %125 = extui %119 {handshake.bb = 6 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %126 = trunci %125 {handshake.bb = 6 : ui32, handshake.name = "index_cast9"} : <i64> to <i32>
    %addressResult_80, %dataResult_81 = store[%126] %116 {handshake.bb = 6 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : <i32>, <f32>, <i32>, <f32>
    %127 = addi %119, %123 {handshake.bb = 6 : ui32, handshake.name = "addi6"} : <i32>
    %128 = cmpi ult, %127, %121 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_82, %falseResult_83 = cond_br %128, %127 {handshake.bb = 6 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_84, %falseResult_85 = cond_br %128, %117 {handshake.bb = 6 : ui32, handshake.name = "cond_br29"} : <i1>, <f32>
    %trueResult_86, %falseResult_87 = cond_br %128, %118 {handshake.bb = 6 : ui32, handshake.name = "cond_br30"} : <i1>, <f32>
    %trueResult_88, %falseResult_89 = cond_br %128, %result_78 {handshake.bb = 6 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %trueResult_90, %falseResult_91 = cond_br %128, %124 {handshake.bb = 6 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %129 = mux %index_93 [%falseResult_91, %trueResult_100] {handshake.bb = 7 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %130 = mux %index_93 [%falseResult_85, %trueResult_102] {handshake.bb = 7 : ui32, handshake.name = "mux21"} : <i1>, [<f32>, <f32>] to <f32>
    %result_92, %index_93 = control_merge [%falseResult_89, %trueResult_104]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %131 = source {handshake.bb = 7 : ui32, handshake.name = "source12"} : <>
    %132 = constant %131 {handshake.bb = 7 : ui32, handshake.name = "constant22", value = 10 : i32} : <>, <i32>
    %133 = source {handshake.bb = 7 : ui32, handshake.name = "source13"} : <>
    %134 = constant %133 {handshake.bb = 7 : ui32, handshake.name = "constant23", value = 1 : i32} : <>, <i32>
    %135 = constant %result_92 {handshake.bb = 7 : ui32, handshake.name = "constant24", value = 0 : i32} : <>, <i32>
    %136 = extui %129 {handshake.bb = 7 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %137 = trunci %136 {handshake.bb = 7 : ui32, handshake.name = "index_cast10"} : <i64> to <i32>
    %addressResult_94, %dataResult_95 = load[%137] %0#1 {handshake.bb = 7 : ui32, handshake.name = "load10"} : <i32>, <f32>, <i32>, <f32>
    %138 = extui %129 {handshake.bb = 7 : ui32, handshake.name = "extui14"} : <i32> to <i64>
    %139 = trunci %138 {handshake.bb = 7 : ui32, handshake.name = "index_cast11"} : <i64> to <i32>
    %addressResult_96, %dataResult_97 = load[%139] %outputs {handshake.bb = 7 : ui32, handshake.name = "load11"} : <i32>, <f32>, <i32>, <f32>
    %140 = addf %dataResult_95, %dataResult_97 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf3"} : <f32>
    %141 = extui %129 {handshake.bb = 7 : ui32, handshake.name = "extui15"} : <i32> to <i64>
    %142 = trunci %141 {handshake.bb = 7 : ui32, handshake.name = "index_cast12"} : <i64> to <i32>
    %addressResult_98, %dataResult_99 = store[%142] %140 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store12"} : <i32>, <f32>, <i32>, <f32>
    %143 = addi %129, %134 {handshake.bb = 7 : ui32, handshake.name = "addi7"} : <i32>
    %144 = cmpi ult, %143, %132 {handshake.bb = 7 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_100, %falseResult_101 = cond_br %144, %143 {handshake.bb = 7 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_102, %falseResult_103 = cond_br %144, %130 {handshake.bb = 7 : ui32, handshake.name = "cond_br34"} : <i1>, <f32>
    %trueResult_104, %falseResult_105 = cond_br %144, %result_92 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <>
    %trueResult_106, %falseResult_107 = cond_br %144, %135 {handshake.bb = 7 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %145 = mux %index_109 [%falseResult_107, %trueResult_134] {handshake.bb = 8 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %146 = mux %index_109 [%falseResult_103, %trueResult_136] {handshake.bb = 8 : ui32, handshake.name = "mux23"} : <i1>, [<f32>, <f32>] to <f32>
    %result_108, %index_109 = control_merge [%falseResult_105, %trueResult_138]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %147 = constant %result_108 {handshake.bb = 8 : ui32, handshake.name = "constant25", value = 0 : i32} : <>, <i32>
    %148 = extui %145 {handshake.bb = 8 : ui32, handshake.name = "extui16"} : <i32> to <i64>
    %149 = trunci %148 {handshake.bb = 8 : ui32, handshake.name = "index_cast13"} : <i64> to <i32>
    %addressResult_110, %dataResult_111 = load[%149] %outputs_2 {handshake.bb = 8 : ui32, handshake.name = "load13"} : <i32>, <f32>, <i32>, <f32>
    %150 = extui %145 {handshake.bb = 8 : ui32, handshake.name = "extui17"} : <i32> to <i64>
    %151 = br %dataResult_111 {handshake.bb = 8 : ui32, handshake.name = "br24"} : <f32>
    %152 = br %147 {handshake.bb = 8 : ui32, handshake.name = "br25"} : <i32>
    %153 = br %146 {handshake.bb = 8 : ui32, handshake.name = "br26"} : <f32>
    %154 = br %145 {handshake.bb = 8 : ui32, handshake.name = "br27"} : <i32>
    %155 = br %150 {handshake.bb = 8 : ui32, handshake.name = "br28"} : <i64>
    %156 = br %result_108 {handshake.bb = 8 : ui32, handshake.name = "br29"} : <>
    %157 = mux %index_113 [%151, %trueResult_118] {handshake.bb = 9 : ui32, handshake.name = "mux24"} : <i1>, [<f32>, <f32>] to <f32>
    %158 = mux %index_113 [%152, %trueResult_120] {handshake.bb = 9 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %159 = mux %index_113 [%153, %trueResult_122] {handshake.bb = 9 : ui32, handshake.name = "mux26"} : <i1>, [<f32>, <f32>] to <f32>
    %160 = mux %index_113 [%154, %trueResult_124] {handshake.bb = 9 : ui32, handshake.name = "mux27"} : <i1>, [<i32>, <i32>] to <i32>
    %161 = mux %index_113 [%155, %trueResult_126] {handshake.bb = 9 : ui32, handshake.name = "mux28"} : <i1>, [<i64>, <i64>] to <i64>
    %result_112, %index_113 = control_merge [%156, %trueResult_128]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>, <>] to <>, <i1>
    %162 = source {handshake.bb = 9 : ui32, handshake.name = "source14"} : <>
    %163 = constant %162 {handshake.bb = 9 : ui32, handshake.name = "constant26", value = 10 : i32} : <>, <i32>
    %164 = source {handshake.bb = 9 : ui32, handshake.name = "source15"} : <>
    %165 = constant %164 {handshake.bb = 9 : ui32, handshake.name = "constant27", value = 1 : i32} : <>, <i32>
    %166 = source {handshake.bb = 9 : ui32, handshake.name = "source16"} : <>
    %167 = constant %166 {handshake.bb = 9 : ui32, handshake.name = "constant28", value = 3 : i64} : <>, <i64>
    %168 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %169 = constant %168 {handshake.bb = 9 : ui32, handshake.name = "constant29", value = 1 : i64} : <>, <i64>
    %170 = extui %158 {handshake.bb = 9 : ui32, handshake.name = "extui18"} : <i32> to <i64>
    %171 = shli %161, %169 {handshake.bb = 9 : ui32, handshake.name = "shli6"} : <i64>
    %172 = shli %161, %167 {handshake.bb = 9 : ui32, handshake.name = "shli7"} : <i64>
    %173 = addi %171, %172 {handshake.bb = 9 : ui32, handshake.name = "addi14"} : <i64>
    %174 = addi %173, %170 {handshake.bb = 9 : ui32, handshake.name = "addi8"} : <i64>
    %175 = trunci %174 {handshake.bb = 9 : ui32, handshake.name = "index_cast14"} : <i64> to <i32>
    %addressResult_114, %dataResult_115 = load[%175] %1#1 {handshake.bb = 9 : ui32, handshake.name = "load14"} : <i32>, <f32>, <i32>, <f32>
    %176 = mulf %dataResult_115, %159 {fastmath = #arith.fastmath<none>, handshake.bb = 9 : ui32, handshake.name = "mulf4"} : <f32>
    %177 = extui %158 {handshake.bb = 9 : ui32, handshake.name = "extui19"} : <i32> to <i64>
    %178 = trunci %177 {handshake.bb = 9 : ui32, handshake.name = "index_cast15"} : <i64> to <i32>
    %addressResult_116, %dataResult_117 = load[%178] %0#2 {handshake.bb = 9 : ui32, handshake.name = "load15"} : <i32>, <f32>, <i32>, <f32>
    %179 = mulf %176, %dataResult_117 {fastmath = #arith.fastmath<none>, handshake.bb = 9 : ui32, handshake.name = "mulf5"} : <f32>
    %180 = addf %157, %179 {fastmath = #arith.fastmath<none>, handshake.bb = 9 : ui32, handshake.name = "addf4"} : <f32>
    %181 = addi %158, %165 {handshake.bb = 9 : ui32, handshake.name = "addi9"} : <i32>
    %182 = cmpi ult, %181, %163 {handshake.bb = 9 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_118, %falseResult_119 = cond_br %182, %180 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <f32>
    %trueResult_120, %falseResult_121 = cond_br %182, %181 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_122, %falseResult_123 = cond_br %182, %159 {handshake.bb = 9 : ui32, handshake.name = "cond_br39"} : <i1>, <f32>
    %trueResult_124, %falseResult_125 = cond_br %182, %160 {handshake.bb = 9 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_126, %falseResult_127 = cond_br %182, %161 {handshake.bb = 9 : ui32, handshake.name = "cond_br41"} : <i1>, <i64>
    %trueResult_128, %falseResult_129 = cond_br %182, %result_112 {handshake.bb = 9 : ui32, handshake.name = "cond_br42"} : <i1>, <>
    %183 = constant %result_130 {handshake.bb = 10 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %184 = merge %falseResult_119 {handshake.bb = 10 : ui32, handshake.name = "merge7"} : <f32>
    %185 = merge %falseResult_123 {handshake.bb = 10 : ui32, handshake.name = "merge8"} : <f32>
    %186 = merge %falseResult_125 {handshake.bb = 10 : ui32, handshake.name = "merge9"} : <i32>
    %result_130, %index_131 = control_merge [%falseResult_129]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %187 = source {handshake.bb = 10 : ui32, handshake.name = "source18"} : <>
    %188 = constant %187 {handshake.bb = 10 : ui32, handshake.name = "constant30", value = 10 : i32} : <>, <i32>
    %189 = source {handshake.bb = 10 : ui32, handshake.name = "source19"} : <>
    %190 = constant %189 {handshake.bb = 10 : ui32, handshake.name = "constant31", value = 1 : i32} : <>, <i32>
    %191 = extui %186 {handshake.bb = 10 : ui32, handshake.name = "extui20"} : <i32> to <i64>
    %192 = trunci %191 {handshake.bb = 10 : ui32, handshake.name = "index_cast16"} : <i64> to <i32>
    %addressResult_132, %dataResult_133 = store[%192] %184 {handshake.bb = 10 : ui32, handshake.name = "store16"} : <i32>, <f32>, <i32>, <f32>
    %193 = addi %186, %190 {handshake.bb = 10 : ui32, handshake.name = "addi10"} : <i32>
    %194 = cmpi ult, %193, %188 {handshake.bb = 10 : ui32, handshake.name = "cmpi6"} : <i32>
    %trueResult_134, %falseResult_135 = cond_br %194, %193 {handshake.bb = 10 : ui32, handshake.name = "cond_br43"} : <i1>, <i32>
    %trueResult_136, %falseResult_137 = cond_br %194, %185 {handshake.bb = 10 : ui32, handshake.name = "cond_br44"} : <i1>, <f32>
    %trueResult_138, %falseResult_139 = cond_br %194, %result_130 {handshake.bb = 10 : ui32, handshake.name = "cond_br45"} : <i1>, <>
    %result_140, %index_141 = control_merge [%falseResult_139]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    end {handshake.bb = 11 : ui32, handshake.name = "end0"} %memEnd_13, %memEnd_11, %memEnd_9, %memEnd_7, %memEnd_5, %memEnd_3, %0#3, %memEnd_1, %memEnd, %arg20 : <>, <>, <>, <>, <>, <>, <>, <>, <>, <>
  }
}

