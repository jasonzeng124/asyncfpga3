module {
  handshake.func @kernel_2mm_float(%arg0: !handshake.channel<f32>, %arg1: !handshake.channel<f32>, %arg2: memref<100xf32>, %arg3: memref<100xf32>, %arg4: memref<100xf32>, %arg5: memref<100xf32>, %arg6: memref<100xf32>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "tmp", "A", "B", "C", "D", "tmp_start", "A_start", "B_start", "C_start", "D_start", "start"], resNames = ["tmp_end", "A_end", "B_end", "C_end", "D_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg6 : memref<100xf32>] %arg11 (%addressResult_64, %180, %addressResult_94, %dataResult_95) %result_118 {connectedBlocks = [7 : i32, 9 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg5 : memref<100xf32>] %arg10 (%addressResult_70) %result_118 {connectedBlocks = [8 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_2, %memEnd_3 = mem_controller[%arg4 : memref<100xf32>] %arg9 (%addressResult_10) %result_118 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_4, %memEnd_5 = mem_controller[%arg3 : memref<100xf32>] %arg8 (%addressResult) %result_118 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0:2 = lsq[%arg2 : memref<100xf32>] (%arg7, %result_30, %addressResult_32, %dataResult_33, %result_66, %addressResult_68, %result_118)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %1 = constant %arg12 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %3 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <f32>
    %4 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <f32>
    %5 = br %arg12 {handshake.bb = 0 : ui32, handshake.name = "br8"} : <>
    %6 = mux %index [%2, %trueResult_50] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %trueResult_52] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %8 = mux %index [%4, %trueResult_54] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%5, %trueResult_56]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %10 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %11 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %12 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %13 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <f32>
    %14 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <f32>
    %15 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i32>
    %16 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i64>
    %17 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <i64>
    %18 = br %result {handshake.bb = 1 : ui32, handshake.name = "br15"} : <>
    %19 = mux %index_7 [%12, %trueResult_34] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %20 = mux %index_7 [%13, %trueResult_36] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %21 = mux %index_7 [%14, %trueResult_38] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %22 = mux %index_7 [%15, %trueResult_40] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %index_7 [%16, %trueResult_42] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %24 = mux %index_7 [%17, %trueResult_44] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %result_6, %index_7 = control_merge [%18, %trueResult_46]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %25 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 0.000000e+00 : f32} : <>, <f32>
    %26 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %27 = extui %19 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %28 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <f32>
    %29 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <i32>
    %30 = br %20 {handshake.bb = 2 : ui32, handshake.name = "br18"} : <f32>
    %31 = br %21 {handshake.bb = 2 : ui32, handshake.name = "br19"} : <f32>
    %32 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br20"} : <i32>
    %33 = br %23 {handshake.bb = 2 : ui32, handshake.name = "br21"} : <i64>
    %34 = br %24 {handshake.bb = 2 : ui32, handshake.name = "br22"} : <i64>
    %35 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br23"} : <i32>
    %36 = br %27 {handshake.bb = 2 : ui32, handshake.name = "br24"} : <i64>
    %37 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br25"} : <>
    %38 = mux %index_9 [%28, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<f32>, <f32>] to <f32>
    %39 = mux %index_9 [%29, %trueResult_12] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %40 = mux %index_9 [%30, %trueResult_14] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %41 = mux %index_9 [%31, %trueResult_16] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<f32>, <f32>] to <f32>
    %42 = mux %index_9 [%32, %trueResult_18] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %43 = mux %index_9 [%33, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<i64>, <i64>] to <i64>
    %44 = mux %index_9 [%34, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i64>, <i64>] to <i64>
    %45 = mux %index_9 [%35, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %46 = mux %index_9 [%36, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux17"} : <i1>, [<i64>, <i64>] to <i64>
    %result_8, %index_9 = control_merge [%37, %trueResult_28]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %47 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %48 = constant %47 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 10 : i32} : <>, <i32>
    %49 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %50 = constant %49 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %52 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %53 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %54 = constant %53 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i64} : <>, <i64>
    %55 = extui %39 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %56 = shli %43, %54 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %57 = shli %43, %52 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %58 = addi %56, %57 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i64>
    %59 = addi %58, %55 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i64>
    %60 = trunci %59 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%60] %outputs_4 {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %61 = mulf %dataResult, %40 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf0"} : <f32>
    %62 = extui %39 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %63 = shli %62, %54 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %64 = shli %62, %52 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %65 = addi %63, %64 {handshake.bb = 3 : ui32, handshake.name = "addi14"} : <i64>
    %66 = addi %65, %46 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i64>
    %67 = trunci %66 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%67] %outputs_2 {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %68 = mulf %61, %dataResult_11 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf1"} : <f32>
    %69 = addf %38, %68 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %70 = addi %39, %50 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %71 = cmpi ult, %70, %48 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %71, %69 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %71, %70 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %71, %40 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_16, %falseResult_17 = cond_br %71, %41 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_18, %falseResult_19 = cond_br %71, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %71, %43 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i64>
    %trueResult_22, %falseResult_23 = cond_br %71, %44 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i64>
    %trueResult_24, %falseResult_25 = cond_br %71, %45 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %71, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_28, %falseResult_29 = cond_br %71, %result_8 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %72 = merge %falseResult {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <f32>
    %73 = merge %falseResult_15 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <f32>
    %74 = merge %falseResult_17 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <f32>
    %75 = merge %falseResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i32>
    %76 = merge %falseResult_21 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i64>
    %77 = merge %falseResult_23 {handshake.bb = 4 : ui32, handshake.name = "merge5"} : <i64>
    %78 = merge %falseResult_25 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i32>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %79 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %80 = constant %79 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 10 : i32} : <>, <i32>
    %81 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %82 = constant %81 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %83 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %84 = constant %83 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 3 : i64} : <>, <i64>
    %85 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %86 = constant %85 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 1 : i64} : <>, <i64>
    %87 = extui %78 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %88 = shli %77, %86 {handshake.bb = 4 : ui32, handshake.name = "shli4"} : <i64>
    %89 = shli %77, %84 {handshake.bb = 4 : ui32, handshake.name = "shli5"} : <i64>
    %90 = addi %88, %89 {handshake.bb = 4 : ui32, handshake.name = "addi15"} : <i64>
    %91 = addi %90, %87 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i64>
    %92 = trunci %91 {handshake.bb = 4 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_32, %dataResult_33 = store[%92] %72 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <f32>, <i32>, <f32>
    %93 = addi %78, %82 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i32>
    %94 = cmpi ult, %93, %80 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %94, %93 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %94, %73 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <f32>
    %trueResult_38, %falseResult_39 = cond_br %94, %74 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_40, %falseResult_41 = cond_br %94, %75 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %94, %76 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i64>
    %trueResult_44, %falseResult_45 = cond_br %94, %77 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i64>
    %trueResult_46, %falseResult_47 = cond_br %94, %result_30 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %95 = merge %falseResult_37 {handshake.bb = 5 : ui32, handshake.name = "merge7"} : <f32>
    %96 = merge %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "merge8"} : <f32>
    %97 = merge %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "merge9"} : <i32>
    %result_48, %index_49 = control_merge [%falseResult_47]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %98 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %99 = constant %98 {handshake.bb = 5 : ui32, handshake.name = "constant18", value = 10 : i32} : <>, <i32>
    %100 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %101 = constant %100 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %102 = constant %result_48 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 0 : i32} : <>, <i32>
    %103 = addi %97, %101 {handshake.bb = 5 : ui32, handshake.name = "addi5"} : <i32>
    %104 = cmpi ult, %103, %99 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_50, %falseResult_51 = cond_br %104, %103 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %104, %95 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <f32>
    %trueResult_54, %falseResult_55 = cond_br %104, %96 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <f32>
    %trueResult_56, %falseResult_57 = cond_br %104, %result_48 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %trueResult_58, %falseResult_59 = cond_br %104, %102 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %105 = mux %index_61 [%falseResult_59, %trueResult_112] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %106 = mux %index_61 [%falseResult_55, %trueResult_114] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<f32>, <f32>] to <f32>
    %result_60, %index_61 = control_merge [%falseResult_57, %trueResult_116]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %107 = constant %result_60 {handshake.bb = 6 : ui32, handshake.name = "constant21", value = 0 : i32} : <>, <i32>
    %108 = extui %105 {handshake.bb = 6 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %109 = extui %105 {handshake.bb = 6 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %110 = extui %105 {handshake.bb = 6 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %111 = br %107 {handshake.bb = 6 : ui32, handshake.name = "br26"} : <i32>
    %112 = br %106 {handshake.bb = 6 : ui32, handshake.name = "br27"} : <f32>
    %113 = br %105 {handshake.bb = 6 : ui32, handshake.name = "br28"} : <i32>
    %114 = br %108 {handshake.bb = 6 : ui32, handshake.name = "br29"} : <i64>
    %115 = br %109 {handshake.bb = 6 : ui32, handshake.name = "br30"} : <i64>
    %116 = br %110 {handshake.bb = 6 : ui32, handshake.name = "br31"} : <i64>
    %117 = br %result_60 {handshake.bb = 6 : ui32, handshake.name = "br32"} : <>
    %118 = mux %index_63 [%111, %trueResult_96] {handshake.bb = 7 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %119 = mux %index_63 [%112, %trueResult_98] {handshake.bb = 7 : ui32, handshake.name = "mux21"} : <i1>, [<f32>, <f32>] to <f32>
    %120 = mux %index_63 [%113, %trueResult_100] {handshake.bb = 7 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %121 = mux %index_63 [%114, %trueResult_102] {handshake.bb = 7 : ui32, handshake.name = "mux23"} : <i1>, [<i64>, <i64>] to <i64>
    %122 = mux %index_63 [%115, %trueResult_104] {handshake.bb = 7 : ui32, handshake.name = "mux24"} : <i1>, [<i64>, <i64>] to <i64>
    %123 = mux %index_63 [%116, %trueResult_106] {handshake.bb = 7 : ui32, handshake.name = "mux25"} : <i1>, [<i64>, <i64>] to <i64>
    %result_62, %index_63 = control_merge [%117, %trueResult_108]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %124 = constant %result_62 {handshake.bb = 7 : ui32, handshake.name = "constant22", value = 0 : i32} : <>, <i32>
    %125 = source {handshake.bb = 7 : ui32, handshake.name = "source10"} : <>
    %126 = constant %125 {handshake.bb = 7 : ui32, handshake.name = "constant23", value = 3 : i64} : <>, <i64>
    %127 = source {handshake.bb = 7 : ui32, handshake.name = "source11"} : <>
    %128 = constant %127 {handshake.bb = 7 : ui32, handshake.name = "constant24", value = 1 : i64} : <>, <i64>
    %129 = extui %118 {handshake.bb = 7 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %130 = shli %121, %128 {handshake.bb = 7 : ui32, handshake.name = "shli6"} : <i64>
    %131 = shli %121, %126 {handshake.bb = 7 : ui32, handshake.name = "shli7"} : <i64>
    %132 = addi %130, %131 {handshake.bb = 7 : ui32, handshake.name = "addi16"} : <i64>
    %133 = addi %132, %129 {handshake.bb = 7 : ui32, handshake.name = "addi6"} : <i64>
    %134 = trunci %133 {handshake.bb = 7 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_64, %dataResult_65 = load[%134] %outputs {handshake.bb = 7 : ui32, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %135 = mulf %dataResult_65, %119 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf2"} : <f32>
    %136 = extui %118 {handshake.bb = 7 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %137 = br %135 {handshake.bb = 7 : ui32, handshake.name = "br33"} : <f32>
    %138 = br %124 {handshake.bb = 7 : ui32, handshake.name = "br34"} : <i32>
    %139 = br %119 {handshake.bb = 7 : ui32, handshake.name = "br35"} : <f32>
    %140 = br %120 {handshake.bb = 7 : ui32, handshake.name = "br36"} : <i32>
    %141 = br %121 {handshake.bb = 7 : ui32, handshake.name = "br37"} : <i64>
    %142 = br %122 {handshake.bb = 7 : ui32, handshake.name = "br38"} : <i64>
    %143 = br %123 {handshake.bb = 7 : ui32, handshake.name = "br39"} : <i64>
    %144 = br %118 {handshake.bb = 7 : ui32, handshake.name = "br40"} : <i32>
    %145 = br %136 {handshake.bb = 7 : ui32, handshake.name = "br41"} : <i64>
    %146 = br %result_62 {handshake.bb = 7 : ui32, handshake.name = "br42"} : <>
    %147 = mux %index_67 [%137, %trueResult_72] {handshake.bb = 8 : ui32, handshake.name = "mux26"} : <i1>, [<f32>, <f32>] to <f32>
    %148 = mux %index_67 [%138, %trueResult_74] {handshake.bb = 8 : ui32, handshake.name = "mux27"} : <i1>, [<i32>, <i32>] to <i32>
    %149 = mux %index_67 [%139, %trueResult_76] {handshake.bb = 8 : ui32, handshake.name = "mux28"} : <i1>, [<f32>, <f32>] to <f32>
    %150 = mux %index_67 [%140, %trueResult_78] {handshake.bb = 8 : ui32, handshake.name = "mux29"} : <i1>, [<i32>, <i32>] to <i32>
    %151 = mux %index_67 [%141, %trueResult_80] {handshake.bb = 8 : ui32, handshake.name = "mux30"} : <i1>, [<i64>, <i64>] to <i64>
    %152 = mux %index_67 [%142, %trueResult_82] {handshake.bb = 8 : ui32, handshake.name = "mux31"} : <i1>, [<i64>, <i64>] to <i64>
    %153 = mux %index_67 [%143, %trueResult_84] {handshake.bb = 8 : ui32, handshake.name = "mux32"} : <i1>, [<i64>, <i64>] to <i64>
    %154 = mux %index_67 [%144, %trueResult_86] {handshake.bb = 8 : ui32, handshake.name = "mux33"} : <i1>, [<i32>, <i32>] to <i32>
    %155 = mux %index_67 [%145, %trueResult_88] {handshake.bb = 8 : ui32, handshake.name = "mux34"} : <i1>, [<i64>, <i64>] to <i64>
    %result_66, %index_67 = control_merge [%146, %trueResult_90]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %156 = source {handshake.bb = 8 : ui32, handshake.name = "source12"} : <>
    %157 = constant %156 {handshake.bb = 8 : ui32, handshake.name = "constant25", value = 10 : i32} : <>, <i32>
    %158 = source {handshake.bb = 8 : ui32, handshake.name = "source13"} : <>
    %159 = constant %158 {handshake.bb = 8 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %160 = source {handshake.bb = 8 : ui32, handshake.name = "source14"} : <>
    %161 = constant %160 {handshake.bb = 8 : ui32, handshake.name = "constant27", value = 3 : i64} : <>, <i64>
    %162 = source {handshake.bb = 8 : ui32, handshake.name = "source15"} : <>
    %163 = constant %162 {handshake.bb = 8 : ui32, handshake.name = "constant28", value = 1 : i64} : <>, <i64>
    %164 = extui %148 {handshake.bb = 8 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %165 = shli %152, %163 {handshake.bb = 8 : ui32, handshake.name = "shli8"} : <i64>
    %166 = shli %152, %161 {handshake.bb = 8 : ui32, handshake.name = "shli9"} : <i64>
    %167 = addi %165, %166 {handshake.bb = 8 : ui32, handshake.name = "addi17"} : <i64>
    %168 = addi %167, %164 {handshake.bb = 8 : ui32, handshake.name = "addi7"} : <i64>
    %169 = trunci %168 {handshake.bb = 8 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_68, %dataResult_69 = load[%169] %0#0 {handshake.bb = 8 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %170 = extui %148 {handshake.bb = 8 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %171 = shli %170, %163 {handshake.bb = 8 : ui32, handshake.name = "shli10"} : <i64>
    %172 = shli %170, %161 {handshake.bb = 8 : ui32, handshake.name = "shli11"} : <i64>
    %173 = addi %171, %172 {handshake.bb = 8 : ui32, handshake.name = "addi18"} : <i64>
    %174 = addi %173, %155 {handshake.bb = 8 : ui32, handshake.name = "addi8"} : <i64>
    %175 = trunci %174 {handshake.bb = 8 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_70, %dataResult_71 = load[%175] %outputs_0 {handshake.bb = 8 : ui32, handshake.name = "load5"} : <i32>, <f32>, <i32>, <f32>
    %176 = mulf %dataResult_69, %dataResult_71 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "mulf3"} : <f32>
    %177 = addf %147, %176 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "addf1"} : <f32>
    %178 = addi %148, %159 {handshake.bb = 8 : ui32, handshake.name = "addi9"} : <i32>
    %179 = cmpi ult, %178, %157 {handshake.bb = 8 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_72, %falseResult_73 = cond_br %179, %177 {handshake.bb = 8 : ui32, handshake.name = "cond_br28"} : <i1>, <f32>
    %trueResult_74, %falseResult_75 = cond_br %179, %178 {handshake.bb = 8 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_76, %falseResult_77 = cond_br %179, %149 {handshake.bb = 8 : ui32, handshake.name = "cond_br30"} : <i1>, <f32>
    %trueResult_78, %falseResult_79 = cond_br %179, %150 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_80, %falseResult_81 = cond_br %179, %151 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <i64>
    %trueResult_82, %falseResult_83 = cond_br %179, %152 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i64>
    %trueResult_84, %falseResult_85 = cond_br %179, %153 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i64>
    %trueResult_86, %falseResult_87 = cond_br %179, %154 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_88, %falseResult_89 = cond_br %179, %155 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i64>
    %trueResult_90, %falseResult_91 = cond_br %179, %result_66 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <>
    %180 = constant %result_92 {handshake.bb = 9 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %181 = merge %falseResult_73 {handshake.bb = 9 : ui32, handshake.name = "merge10"} : <f32>
    %182 = merge %falseResult_77 {handshake.bb = 9 : ui32, handshake.name = "merge11"} : <f32>
    %183 = merge %falseResult_79 {handshake.bb = 9 : ui32, handshake.name = "merge12"} : <i32>
    %184 = merge %falseResult_81 {handshake.bb = 9 : ui32, handshake.name = "merge13"} : <i64>
    %185 = merge %falseResult_83 {handshake.bb = 9 : ui32, handshake.name = "merge14"} : <i64>
    %186 = merge %falseResult_85 {handshake.bb = 9 : ui32, handshake.name = "merge15"} : <i64>
    %187 = merge %falseResult_87 {handshake.bb = 9 : ui32, handshake.name = "merge16"} : <i32>
    %result_92, %index_93 = control_merge [%falseResult_91]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %188 = source {handshake.bb = 9 : ui32, handshake.name = "source16"} : <>
    %189 = constant %188 {handshake.bb = 9 : ui32, handshake.name = "constant29", value = 10 : i32} : <>, <i32>
    %190 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %191 = constant %190 {handshake.bb = 9 : ui32, handshake.name = "constant30", value = 1 : i32} : <>, <i32>
    %192 = source {handshake.bb = 9 : ui32, handshake.name = "source18"} : <>
    %193 = constant %192 {handshake.bb = 9 : ui32, handshake.name = "constant31", value = 3 : i64} : <>, <i64>
    %194 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %195 = constant %194 {handshake.bb = 9 : ui32, handshake.name = "constant32", value = 1 : i64} : <>, <i64>
    %196 = extui %187 {handshake.bb = 9 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %197 = shli %186, %195 {handshake.bb = 9 : ui32, handshake.name = "shli12"} : <i64>
    %198 = shli %186, %193 {handshake.bb = 9 : ui32, handshake.name = "shli13"} : <i64>
    %199 = addi %197, %198 {handshake.bb = 9 : ui32, handshake.name = "addi19"} : <i64>
    %200 = addi %199, %196 {handshake.bb = 9 : ui32, handshake.name = "addi10"} : <i64>
    %201 = trunci %200 {handshake.bb = 9 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_94, %dataResult_95 = store[%201] %181 {handshake.bb = 9 : ui32, handshake.name = "store6"} : <i32>, <f32>, <i32>, <f32>
    %202 = addi %187, %191 {handshake.bb = 9 : ui32, handshake.name = "addi11"} : <i32>
    %203 = cmpi ult, %202, %189 {handshake.bb = 9 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_96, %falseResult_97 = cond_br %203, %202 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_98, %falseResult_99 = cond_br %203, %182 {handshake.bb = 9 : ui32, handshake.name = "cond_br39"} : <i1>, <f32>
    %trueResult_100, %falseResult_101 = cond_br %203, %183 {handshake.bb = 9 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_102, %falseResult_103 = cond_br %203, %184 {handshake.bb = 9 : ui32, handshake.name = "cond_br41"} : <i1>, <i64>
    %trueResult_104, %falseResult_105 = cond_br %203, %185 {handshake.bb = 9 : ui32, handshake.name = "cond_br42"} : <i1>, <i64>
    %trueResult_106, %falseResult_107 = cond_br %203, %186 {handshake.bb = 9 : ui32, handshake.name = "cond_br43"} : <i1>, <i64>
    %trueResult_108, %falseResult_109 = cond_br %203, %result_92 {handshake.bb = 9 : ui32, handshake.name = "cond_br44"} : <i1>, <>
    %204 = merge %falseResult_99 {handshake.bb = 10 : ui32, handshake.name = "merge17"} : <f32>
    %205 = merge %falseResult_101 {handshake.bb = 10 : ui32, handshake.name = "merge18"} : <i32>
    %result_110, %index_111 = control_merge [%falseResult_109]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %206 = source {handshake.bb = 10 : ui32, handshake.name = "source20"} : <>
    %207 = constant %206 {handshake.bb = 10 : ui32, handshake.name = "constant33", value = 10 : i32} : <>, <i32>
    %208 = source {handshake.bb = 10 : ui32, handshake.name = "source21"} : <>
    %209 = constant %208 {handshake.bb = 10 : ui32, handshake.name = "constant34", value = 1 : i32} : <>, <i32>
    %210 = addi %205, %209 {handshake.bb = 10 : ui32, handshake.name = "addi12"} : <i32>
    %211 = cmpi ult, %210, %207 {handshake.bb = 10 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_112, %falseResult_113 = cond_br %211, %210 {handshake.bb = 10 : ui32, handshake.name = "cond_br45"} : <i1>, <i32>
    %trueResult_114, %falseResult_115 = cond_br %211, %204 {handshake.bb = 10 : ui32, handshake.name = "cond_br46"} : <i1>, <f32>
    %trueResult_116, %falseResult_117 = cond_br %211, %result_110 {handshake.bb = 10 : ui32, handshake.name = "cond_br47"} : <i1>, <>
    %result_118, %index_119 = control_merge [%falseResult_117]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    end {handshake.bb = 11 : ui32, handshake.name = "end0"} %0#1, %memEnd_5, %memEnd_3, %memEnd_1, %memEnd, %arg12 : <>, <>, <>, <>, <>, <>
  }
}

