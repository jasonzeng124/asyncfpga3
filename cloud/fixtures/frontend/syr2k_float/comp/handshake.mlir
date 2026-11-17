module {
  handshake.func @syr2k_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<900xf32>, %arg3: !handshake.channel<f32>, %arg4: !handshake.channel<f32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "alpha", "beta", "A_start", "B_start", "C_start", "start"], resNames = ["A_end", "B_end", "C_end", "end"]} {
    %0:3 = lsq[%arg2 : memref<900xf32>] (%arg7, %result_2, %addressResult, %addressResult_4, %dataResult_5, %result_30, %addressResult_32, %result_68, %addressResult_70, %dataResult_71, %result_96)  {groupSizes = [2 : i32, 1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<900xf32>] %arg6 (%addressResult_38, %addressResult_40) %result_96 {connectedBlocks = [6 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<900xf32>] %arg5 (%addressResult_36, %addressResult_42) %result_96 {connectedBlocks = [6 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <f32>
    %5 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <>
    %6 = mux %index [%2, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %8 = mux %index [%4, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%5, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %10 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %11 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %13 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <f32>
    %14 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i32>
    %15 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %16 = br %result {handshake.bb = 1 : ui32, handshake.name = "br13"} : <>
    %17 = mux %index_3 [%11, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_3 [%12, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %19 = mux %index_3 [%13, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %20 = mux %index_3 [%14, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %21 = mux %index_3 [%15, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %result_2, %index_3 = control_merge [%16, %trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 10 : i32} : <>, <i32>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %34 = extui %17 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %35 = shli %21, %33 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %36 = shli %21, %31 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %37 = addi %35, %36 {handshake.bb = 2 : ui32, handshake.name = "addi12"} : <i64>
    %38 = shli %21, %29 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %39 = shli %21, %27 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %40 = addi %38, %39 {handshake.bb = 2 : ui32, handshake.name = "addi13"} : <i64>
    %41 = addi %37, %40 {handshake.bb = 2 : ui32, handshake.name = "addi14"} : <i64>
    %42 = addi %41, %34 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %43 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%43] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %44 = mulf %dataResult, %19 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %45 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = store[%45] %44 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <f32>, <i32>, <f32>
    %46 = addi %17, %25 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %47 = cmpi ult, %46, %23 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %47, %46 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %47, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_8, %falseResult_9 = cond_br %47, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_10, %falseResult_11 = cond_br %47, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %47, %21 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_14, %falseResult_15 = cond_br %47, %result_2 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %48 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %49 = merge %falseResult_9 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <f32>
    %50 = merge %falseResult_11 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %52 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 10 : i32} : <>, <i32>
    %53 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %54 = constant %53 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %55 = constant %result_16 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 0 : i32} : <>, <i32>
    %56 = addi %50, %54 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %57 = cmpi ult, %56, %52 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %57, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %57, %48 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_22, %falseResult_23 = cond_br %57, %49 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <f32>
    %trueResult_24, %falseResult_25 = cond_br %57, %result_16 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %trueResult_26, %falseResult_27 = cond_br %57, %55 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %58 = mux %index_29 [%falseResult_27, %trueResult_90] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %59 = mux %index_29 [%falseResult_21, %trueResult_92] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<f32>, <f32>] to <f32>
    %result_28, %index_29 = control_merge [%falseResult_25, %trueResult_94]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %60 = constant %result_28 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 0 : i32} : <>, <i32>
    %61 = extui %58 {handshake.bb = 4 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %62 = extui %58 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %63 = extui %58 {handshake.bb = 4 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %64 = extui %58 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %65 = br %60 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <i32>
    %66 = br %59 {handshake.bb = 4 : ui32, handshake.name = "br15"} : <f32>
    %67 = br %58 {handshake.bb = 4 : ui32, handshake.name = "br16"} : <i32>
    %68 = br %61 {handshake.bb = 4 : ui32, handshake.name = "br17"} : <i64>
    %69 = br %62 {handshake.bb = 4 : ui32, handshake.name = "br18"} : <i64>
    %70 = br %63 {handshake.bb = 4 : ui32, handshake.name = "br19"} : <i64>
    %71 = br %64 {handshake.bb = 4 : ui32, handshake.name = "br20"} : <i64>
    %72 = br %result_28 {handshake.bb = 4 : ui32, handshake.name = "br21"} : <>
    %73 = mux %index_31 [%65, %trueResult_72] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %74 = mux %index_31 [%66, %trueResult_74] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %75 = mux %index_31 [%67, %trueResult_76] {handshake.bb = 5 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %76 = mux %index_31 [%68, %trueResult_78] {handshake.bb = 5 : ui32, handshake.name = "mux13"} : <i1>, [<i64>, <i64>] to <i64>
    %77 = mux %index_31 [%69, %trueResult_80] {handshake.bb = 5 : ui32, handshake.name = "mux14"} : <i1>, [<i64>, <i64>] to <i64>
    %78 = mux %index_31 [%70, %trueResult_82] {handshake.bb = 5 : ui32, handshake.name = "mux15"} : <i1>, [<i64>, <i64>] to <i64>
    %79 = mux %index_31 [%71, %trueResult_84] {handshake.bb = 5 : ui32, handshake.name = "mux16"} : <i1>, [<i64>, <i64>] to <i64>
    %result_30, %index_31 = control_merge [%72, %trueResult_86]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %80 = constant %result_30 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 0 : i32} : <>, <i32>
    %81 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %82 = constant %81 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 4 : i64} : <>, <i64>
    %83 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %84 = constant %83 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = 3 : i64} : <>, <i64>
    %85 = source {handshake.bb = 5 : ui32, handshake.name = "source10"} : <>
    %86 = constant %85 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 2 : i64} : <>, <i64>
    %87 = source {handshake.bb = 5 : ui32, handshake.name = "source11"} : <>
    %88 = constant %87 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 1 : i64} : <>, <i64>
    %89 = extui %73 {handshake.bb = 5 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %90 = shli %76, %88 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %91 = shli %76, %86 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %92 = addi %90, %91 {handshake.bb = 5 : ui32, handshake.name = "addi15"} : <i64>
    %93 = shli %76, %84 {handshake.bb = 5 : ui32, handshake.name = "shli6"} : <i64>
    %94 = shli %76, %82 {handshake.bb = 5 : ui32, handshake.name = "shli7"} : <i64>
    %95 = addi %93, %94 {handshake.bb = 5 : ui32, handshake.name = "addi16"} : <i64>
    %96 = addi %92, %95 {handshake.bb = 5 : ui32, handshake.name = "addi17"} : <i64>
    %97 = addi %96, %89 {handshake.bb = 5 : ui32, handshake.name = "addi3"} : <i64>
    %98 = trunci %97 {handshake.bb = 5 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_32, %dataResult_33 = load[%98] %0#1 {handshake.bb = 5 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %99 = extui %73 {handshake.bb = 5 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %100 = extui %73 {handshake.bb = 5 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %101 = br %dataResult_33 {handshake.bb = 5 : ui32, handshake.name = "br22"} : <f32>
    %102 = br %80 {handshake.bb = 5 : ui32, handshake.name = "br23"} : <i32>
    %103 = br %74 {handshake.bb = 5 : ui32, handshake.name = "br24"} : <f32>
    %104 = br %75 {handshake.bb = 5 : ui32, handshake.name = "br25"} : <i32>
    %105 = br %76 {handshake.bb = 5 : ui32, handshake.name = "br26"} : <i64>
    %106 = br %77 {handshake.bb = 5 : ui32, handshake.name = "br27"} : <i64>
    %107 = br %78 {handshake.bb = 5 : ui32, handshake.name = "br28"} : <i64>
    %108 = br %79 {handshake.bb = 5 : ui32, handshake.name = "br29"} : <i64>
    %109 = br %73 {handshake.bb = 5 : ui32, handshake.name = "br30"} : <i32>
    %110 = br %99 {handshake.bb = 5 : ui32, handshake.name = "br31"} : <i64>
    %111 = br %100 {handshake.bb = 5 : ui32, handshake.name = "br32"} : <i64>
    %112 = br %result_30 {handshake.bb = 5 : ui32, handshake.name = "br33"} : <>
    %113 = mux %index_35 [%101, %trueResult_44] {handshake.bb = 6 : ui32, handshake.name = "mux17"} : <i1>, [<f32>, <f32>] to <f32>
    %114 = mux %index_35 [%102, %trueResult_46] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %115 = mux %index_35 [%103, %trueResult_48] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<f32>, <f32>] to <f32>
    %116 = mux %index_35 [%104, %trueResult_50] {handshake.bb = 6 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %117 = mux %index_35 [%105, %trueResult_52] {handshake.bb = 6 : ui32, handshake.name = "mux21"} : <i1>, [<i64>, <i64>] to <i64>
    %118 = mux %index_35 [%106, %trueResult_54] {handshake.bb = 6 : ui32, handshake.name = "mux22"} : <i1>, [<i64>, <i64>] to <i64>
    %119 = mux %index_35 [%107, %trueResult_56] {handshake.bb = 6 : ui32, handshake.name = "mux23"} : <i1>, [<i64>, <i64>] to <i64>
    %120 = mux %index_35 [%108, %trueResult_58] {handshake.bb = 6 : ui32, handshake.name = "mux24"} : <i1>, [<i64>, <i64>] to <i64>
    %121 = mux %index_35 [%109, %trueResult_60] {handshake.bb = 6 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %122 = mux %index_35 [%110, %trueResult_62] {handshake.bb = 6 : ui32, handshake.name = "mux26"} : <i1>, [<i64>, <i64>] to <i64>
    %123 = mux %index_35 [%111, %trueResult_64] {handshake.bb = 6 : ui32, handshake.name = "mux27"} : <i1>, [<i64>, <i64>] to <i64>
    %result_34, %index_35 = control_merge [%112, %trueResult_66]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %124 = source {handshake.bb = 6 : ui32, handshake.name = "source12"} : <>
    %125 = constant %124 {handshake.bb = 6 : ui32, handshake.name = "constant24", value = 10 : i32} : <>, <i32>
    %126 = source {handshake.bb = 6 : ui32, handshake.name = "source13"} : <>
    %127 = constant %126 {handshake.bb = 6 : ui32, handshake.name = "constant25", value = 1 : i32} : <>, <i32>
    %128 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %129 = constant %128 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 4 : i64} : <>, <i64>
    %130 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %131 = constant %130 {handshake.bb = 6 : ui32, handshake.name = "constant27", value = 3 : i64} : <>, <i64>
    %132 = source {handshake.bb = 6 : ui32, handshake.name = "source16"} : <>
    %133 = constant %132 {handshake.bb = 6 : ui32, handshake.name = "constant28", value = 2 : i64} : <>, <i64>
    %134 = source {handshake.bb = 6 : ui32, handshake.name = "source17"} : <>
    %135 = constant %134 {handshake.bb = 6 : ui32, handshake.name = "constant29", value = 1 : i64} : <>, <i64>
    %136 = extui %114 {handshake.bb = 6 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %137 = shli %118, %135 {handshake.bb = 6 : ui32, handshake.name = "shli8"} : <i64>
    %138 = shli %118, %133 {handshake.bb = 6 : ui32, handshake.name = "shli9"} : <i64>
    %139 = addi %137, %138 {handshake.bb = 6 : ui32, handshake.name = "addi18"} : <i64>
    %140 = shli %118, %131 {handshake.bb = 6 : ui32, handshake.name = "shli10"} : <i64>
    %141 = shli %118, %129 {handshake.bb = 6 : ui32, handshake.name = "shli11"} : <i64>
    %142 = addi %140, %141 {handshake.bb = 6 : ui32, handshake.name = "addi19"} : <i64>
    %143 = addi %139, %142 {handshake.bb = 6 : ui32, handshake.name = "addi20"} : <i64>
    %144 = addi %143, %136 {handshake.bb = 6 : ui32, handshake.name = "addi4"} : <i64>
    %145 = trunci %144 {handshake.bb = 6 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_36, %dataResult_37 = load[%145] %outputs_0#0 {handshake.bb = 6 : ui32, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %146 = mulf %dataResult_37, %115 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf1"} : <f32>
    %147 = extui %114 {handshake.bb = 6 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %148 = shli %122, %135 {handshake.bb = 6 : ui32, handshake.name = "shli12"} : <i64>
    %149 = shli %122, %133 {handshake.bb = 6 : ui32, handshake.name = "shli13"} : <i64>
    %150 = addi %148, %149 {handshake.bb = 6 : ui32, handshake.name = "addi21"} : <i64>
    %151 = shli %122, %131 {handshake.bb = 6 : ui32, handshake.name = "shli14"} : <i64>
    %152 = shli %122, %129 {handshake.bb = 6 : ui32, handshake.name = "shli15"} : <i64>
    %153 = addi %151, %152 {handshake.bb = 6 : ui32, handshake.name = "addi22"} : <i64>
    %154 = addi %150, %153 {handshake.bb = 6 : ui32, handshake.name = "addi23"} : <i64>
    %155 = addi %154, %147 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i64>
    %156 = trunci %155 {handshake.bb = 6 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_38, %dataResult_39 = load[%156] %outputs#0 {handshake.bb = 6 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %157 = mulf %146, %dataResult_39 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf2"} : <f32>
    %158 = addf %113, %157 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf0"} : <f32>
    %159 = extui %114 {handshake.bb = 6 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %160 = shli %119, %135 {handshake.bb = 6 : ui32, handshake.name = "shli16"} : <i64>
    %161 = shli %119, %133 {handshake.bb = 6 : ui32, handshake.name = "shli17"} : <i64>
    %162 = addi %160, %161 {handshake.bb = 6 : ui32, handshake.name = "addi24"} : <i64>
    %163 = shli %119, %131 {handshake.bb = 6 : ui32, handshake.name = "shli18"} : <i64>
    %164 = shli %119, %129 {handshake.bb = 6 : ui32, handshake.name = "shli19"} : <i64>
    %165 = addi %163, %164 {handshake.bb = 6 : ui32, handshake.name = "addi25"} : <i64>
    %166 = addi %162, %165 {handshake.bb = 6 : ui32, handshake.name = "addi26"} : <i64>
    %167 = addi %166, %159 {handshake.bb = 6 : ui32, handshake.name = "addi6"} : <i64>
    %168 = trunci %167 {handshake.bb = 6 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_40, %dataResult_41 = load[%168] %outputs#1 {handshake.bb = 6 : ui32, handshake.name = "load5"} : <i32>, <f32>, <i32>, <f32>
    %169 = mulf %dataResult_41, %115 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf3"} : <f32>
    %170 = extui %114 {handshake.bb = 6 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %171 = shli %123, %135 {handshake.bb = 6 : ui32, handshake.name = "shli20"} : <i64>
    %172 = shli %123, %133 {handshake.bb = 6 : ui32, handshake.name = "shli21"} : <i64>
    %173 = addi %171, %172 {handshake.bb = 6 : ui32, handshake.name = "addi27"} : <i64>
    %174 = shli %123, %131 {handshake.bb = 6 : ui32, handshake.name = "shli22"} : <i64>
    %175 = shli %123, %129 {handshake.bb = 6 : ui32, handshake.name = "shli23"} : <i64>
    %176 = addi %174, %175 {handshake.bb = 6 : ui32, handshake.name = "addi28"} : <i64>
    %177 = addi %173, %176 {handshake.bb = 6 : ui32, handshake.name = "addi29"} : <i64>
    %178 = addi %177, %170 {handshake.bb = 6 : ui32, handshake.name = "addi7"} : <i64>
    %179 = trunci %178 {handshake.bb = 6 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_42, %dataResult_43 = load[%179] %outputs_0#1 {handshake.bb = 6 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %180 = mulf %169, %dataResult_43 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf4"} : <f32>
    %181 = addf %158, %180 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf1"} : <f32>
    %182 = addi %114, %127 {handshake.bb = 6 : ui32, handshake.name = "addi8"} : <i32>
    %183 = cmpi ult, %182, %125 {handshake.bb = 6 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %183, %181 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    %trueResult_46, %falseResult_47 = cond_br %183, %182 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_48, %falseResult_49 = cond_br %183, %115 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_50, %falseResult_51 = cond_br %183, %116 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %183, %117 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <i64>
    %trueResult_54, %falseResult_55 = cond_br %183, %118 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i64>
    %trueResult_56, %falseResult_57 = cond_br %183, %119 {handshake.bb = 6 : ui32, handshake.name = "cond_br22"} : <i1>, <i64>
    %trueResult_58, %falseResult_59 = cond_br %183, %120 {handshake.bb = 6 : ui32, handshake.name = "cond_br23"} : <i1>, <i64>
    %trueResult_60, %falseResult_61 = cond_br %183, %121 {handshake.bb = 6 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %183, %122 {handshake.bb = 6 : ui32, handshake.name = "cond_br25"} : <i1>, <i64>
    %trueResult_64, %falseResult_65 = cond_br %183, %123 {handshake.bb = 6 : ui32, handshake.name = "cond_br26"} : <i1>, <i64>
    %trueResult_66, %falseResult_67 = cond_br %183, %result_34 {handshake.bb = 6 : ui32, handshake.name = "cond_br27"} : <i1>, <>
    %184 = merge %falseResult_45 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <f32>
    %185 = merge %falseResult_49 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <f32>
    %186 = merge %falseResult_51 {handshake.bb = 7 : ui32, handshake.name = "merge5"} : <i32>
    %187 = merge %falseResult_53 {handshake.bb = 7 : ui32, handshake.name = "merge6"} : <i64>
    %188 = merge %falseResult_55 {handshake.bb = 7 : ui32, handshake.name = "merge7"} : <i64>
    %189 = merge %falseResult_57 {handshake.bb = 7 : ui32, handshake.name = "merge8"} : <i64>
    %190 = merge %falseResult_59 {handshake.bb = 7 : ui32, handshake.name = "merge9"} : <i64>
    %191 = merge %falseResult_61 {handshake.bb = 7 : ui32, handshake.name = "merge10"} : <i32>
    %result_68, %index_69 = control_merge [%falseResult_67]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    %192 = source {handshake.bb = 7 : ui32, handshake.name = "source18"} : <>
    %193 = constant %192 {handshake.bb = 7 : ui32, handshake.name = "constant30", value = 10 : i32} : <>, <i32>
    %194 = source {handshake.bb = 7 : ui32, handshake.name = "source19"} : <>
    %195 = constant %194 {handshake.bb = 7 : ui32, handshake.name = "constant31", value = 1 : i32} : <>, <i32>
    %196 = source {handshake.bb = 7 : ui32, handshake.name = "source20"} : <>
    %197 = constant %196 {handshake.bb = 7 : ui32, handshake.name = "constant32", value = 4 : i64} : <>, <i64>
    %198 = source {handshake.bb = 7 : ui32, handshake.name = "source21"} : <>
    %199 = constant %198 {handshake.bb = 7 : ui32, handshake.name = "constant33", value = 3 : i64} : <>, <i64>
    %200 = source {handshake.bb = 7 : ui32, handshake.name = "source22"} : <>
    %201 = constant %200 {handshake.bb = 7 : ui32, handshake.name = "constant34", value = 2 : i64} : <>, <i64>
    %202 = source {handshake.bb = 7 : ui32, handshake.name = "source23"} : <>
    %203 = constant %202 {handshake.bb = 7 : ui32, handshake.name = "constant35", value = 1 : i64} : <>, <i64>
    %204 = extui %191 {handshake.bb = 7 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %205 = shli %190, %203 {handshake.bb = 7 : ui32, handshake.name = "shli24"} : <i64>
    %206 = shli %190, %201 {handshake.bb = 7 : ui32, handshake.name = "shli25"} : <i64>
    %207 = addi %205, %206 {handshake.bb = 7 : ui32, handshake.name = "addi30"} : <i64>
    %208 = shli %190, %199 {handshake.bb = 7 : ui32, handshake.name = "shli26"} : <i64>
    %209 = shli %190, %197 {handshake.bb = 7 : ui32, handshake.name = "shli27"} : <i64>
    %210 = addi %208, %209 {handshake.bb = 7 : ui32, handshake.name = "addi31"} : <i64>
    %211 = addi %207, %210 {handshake.bb = 7 : ui32, handshake.name = "addi32"} : <i64>
    %212 = addi %211, %204 {handshake.bb = 7 : ui32, handshake.name = "addi9"} : <i64>
    %213 = trunci %212 {handshake.bb = 7 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_70, %dataResult_71 = store[%213] %184 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : <i32>, <f32>, <i32>, <f32>
    %214 = addi %191, %195 {handshake.bb = 7 : ui32, handshake.name = "addi10"} : <i32>
    %215 = cmpi ult, %214, %193 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_72, %falseResult_73 = cond_br %215, %214 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %215, %185 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <f32>
    %trueResult_76, %falseResult_77 = cond_br %215, %186 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_78, %falseResult_79 = cond_br %215, %187 {handshake.bb = 7 : ui32, handshake.name = "cond_br31"} : <i1>, <i64>
    %trueResult_80, %falseResult_81 = cond_br %215, %188 {handshake.bb = 7 : ui32, handshake.name = "cond_br32"} : <i1>, <i64>
    %trueResult_82, %falseResult_83 = cond_br %215, %189 {handshake.bb = 7 : ui32, handshake.name = "cond_br33"} : <i1>, <i64>
    %trueResult_84, %falseResult_85 = cond_br %215, %190 {handshake.bb = 7 : ui32, handshake.name = "cond_br34"} : <i1>, <i64>
    %trueResult_86, %falseResult_87 = cond_br %215, %result_68 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <>
    %216 = merge %falseResult_75 {handshake.bb = 8 : ui32, handshake.name = "merge11"} : <f32>
    %217 = merge %falseResult_77 {handshake.bb = 8 : ui32, handshake.name = "merge12"} : <i32>
    %result_88, %index_89 = control_merge [%falseResult_87]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    %218 = source {handshake.bb = 8 : ui32, handshake.name = "source24"} : <>
    %219 = constant %218 {handshake.bb = 8 : ui32, handshake.name = "constant36", value = 10 : i32} : <>, <i32>
    %220 = source {handshake.bb = 8 : ui32, handshake.name = "source25"} : <>
    %221 = constant %220 {handshake.bb = 8 : ui32, handshake.name = "constant37", value = 1 : i32} : <>, <i32>
    %222 = addi %217, %221 {handshake.bb = 8 : ui32, handshake.name = "addi11"} : <i32>
    %223 = cmpi ult, %222, %219 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_90, %falseResult_91 = cond_br %223, %222 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_92, %falseResult_93 = cond_br %223, %216 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <f32>
    %trueResult_94, %falseResult_95 = cond_br %223, %result_88 {handshake.bb = 8 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %result_96, %index_97 = control_merge [%falseResult_95]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    end {handshake.bb = 9 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#2, %arg8 : <>, <>, <>, <>
  }
}

