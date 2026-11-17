module {
  handshake.func @covariance_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<30xf32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["data", "symmat", "mean", "data_start", "symmat_start", "mean_start", "start"], resNames = ["data_end", "symmat_end", "mean_end", "end"]} {
    %0:2 = lsq[%arg2 : memref<30xf32>] (%arg5, %result_10, %addressResult_12, %dataResult_13, %result_22, %addressResult_24, %result_88)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %1 = lsq[%arg1 : memref<900xf32>] (%arg4, %result_70, %addressResult_72, %dataResult_73, %addressResult_74, %dataResult_75, %result_88)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> !handshake.control<>
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<900xf32>] %arg3 (%65, %addressResult_26, %2#3, %2#4, %2#5) %result_88 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %2:6 = lsq[MC] (%result_0, %addressResult, %result_22, %addressResult_28, %dataResult_29, %result_50, %addressResult_52, %addressResult_54, %outputs#1)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>)
    %3 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %5 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %6 = mux %index [%4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 0.000000e+00 : f32} : <>, <f32>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %9 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <f32>
    %11 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %12 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %13 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i64>
    %14 = br %result {handshake.bb = 1 : ui32, handshake.name = "br11"} : <>
    %15 = mux %index_1 [%10, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %16 = mux %index_1 [%11, %trueResult_2] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_1 [%12, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_1 [%13, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_0, %index_1 = control_merge [%14, %trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 30 : i32} : <>, <i32>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 4 : i64} : <>, <i64>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 3 : i64} : <>, <i64>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 2 : i64} : <>, <i64>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant17", value = 1 : i64} : <>, <i64>
    %31 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %32 = shli %31, %30 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %33 = shli %31, %28 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %34 = addi %32, %33 {handshake.bb = 2 : ui32, handshake.name = "addi13"} : <i64>
    %35 = shli %31, %26 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %36 = shli %31, %24 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %37 = addi %35, %36 {handshake.bb = 2 : ui32, handshake.name = "addi14"} : <i64>
    %38 = addi %34, %37 {handshake.bb = 2 : ui32, handshake.name = "addi15"} : <i64>
    %39 = addi %38, %18 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %40 = trunci %39 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%40] %2#0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %41 = addf %15, %dataResult {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %42 = addi %16, %22 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %43 = cmpi ult, %42, %20 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %43, %41 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_2, %falseResult_3 = cond_br %43, %42 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %43, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %43, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i64>
    %trueResult_8, %falseResult_9 = cond_br %43, %result_0 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %44 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %45 = merge %falseResult_5 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_9]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %47 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 3.000000e+01 : f32} : <>, <f32>
    %48 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %49 = constant %48 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 30 : i32} : <>, <i32>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %52 = constant %result_10 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 0 : i32} : <>, <i32>
    %53 = divf %44, %47 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "divf0"} : <f32>
    %54 = extui %45 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %55 = trunci %54 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%55] %53 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <f32>, <i32>, <f32>
    %56 = addi %45, %51 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %57 = cmpi ult, %56, %49 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %57, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %57, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_18, %falseResult_19 = cond_br %57, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %58 = mux %index_21 [%falseResult_19, %trueResult_40] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_17, %trueResult_42]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %59 = constant %result_20 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 0 : i32} : <>, <i32>
    %60 = extui %58 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %61 = br %59 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i32>
    %62 = br %58 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <i32>
    %63 = br %60 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <i64>
    %64 = br %result_20 {handshake.bb = 4 : ui32, handshake.name = "br15"} : <>
    %65 = constant %result_22 {handshake.bb = 5 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %66 = mux %index_23 [%61, %trueResult_30] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %67 = mux %index_23 [%62, %trueResult_32] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %68 = mux %index_23 [%63, %trueResult_34] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %result_22, %index_23 = control_merge [%64, %trueResult_36]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %69 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %70 = constant %69 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 30 : i32} : <>, <i32>
    %71 = source {handshake.bb = 5 : ui32, handshake.name = "source10"} : <>
    %72 = constant %71 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i32} : <>, <i32>
    %73 = source {handshake.bb = 5 : ui32, handshake.name = "source11"} : <>
    %74 = constant %73 {handshake.bb = 5 : ui32, handshake.name = "constant25", value = 4 : i64} : <>, <i64>
    %75 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %76 = constant %75 {handshake.bb = 5 : ui32, handshake.name = "constant26", value = 3 : i64} : <>, <i64>
    %77 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %78 = constant %77 {handshake.bb = 5 : ui32, handshake.name = "constant27", value = 2 : i64} : <>, <i64>
    %79 = source {handshake.bb = 5 : ui32, handshake.name = "source14"} : <>
    %80 = constant %79 {handshake.bb = 5 : ui32, handshake.name = "constant28", value = 1 : i64} : <>, <i64>
    %81 = extui %66 {handshake.bb = 5 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %82 = trunci %81 {handshake.bb = 5 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = load[%82] %0#0 {handshake.bb = 5 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %83 = extui %66 {handshake.bb = 5 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %84 = shli %68, %80 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %85 = shli %68, %78 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %86 = addi %84, %85 {handshake.bb = 5 : ui32, handshake.name = "addi16"} : <i64>
    %87 = shli %68, %76 {handshake.bb = 5 : ui32, handshake.name = "shli6"} : <i64>
    %88 = shli %68, %74 {handshake.bb = 5 : ui32, handshake.name = "shli7"} : <i64>
    %89 = addi %87, %88 {handshake.bb = 5 : ui32, handshake.name = "addi17"} : <i64>
    %90 = addi %86, %89 {handshake.bb = 5 : ui32, handshake.name = "addi18"} : <i64>
    %91 = addi %90, %83 {handshake.bb = 5 : ui32, handshake.name = "addi3"} : <i64>
    %92 = trunci %91 {handshake.bb = 5 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_26, %dataResult_27 = load[%92] %outputs#0 {handshake.bb = 5 : ui32, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %93 = subf %dataResult_27, %dataResult_25 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "subf0"} : <f32>
    %94 = trunci %91 {handshake.bb = 5 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_28, %dataResult_29 = store[%94] %93 {handshake.bb = 5 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <f32>, <i32>, <f32>
    %95 = addi %66, %72 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i32>
    %96 = cmpi ult, %95, %70 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %96, %95 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %96, %67 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %96, %68 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i64>
    %trueResult_36, %falseResult_37 = cond_br %96, %result_22 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %97 = merge %falseResult_33 {handshake.bb = 6 : ui32, handshake.name = "merge2"} : <i32>
    %result_38, %index_39 = control_merge [%falseResult_37]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %98 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %99 = constant %98 {handshake.bb = 6 : ui32, handshake.name = "constant29", value = 30 : i32} : <>, <i32>
    %100 = source {handshake.bb = 6 : ui32, handshake.name = "source16"} : <>
    %101 = constant %100 {handshake.bb = 6 : ui32, handshake.name = "constant30", value = 1 : i32} : <>, <i32>
    %102 = constant %result_38 {handshake.bb = 6 : ui32, handshake.name = "constant31", value = 0 : i32} : <>, <i32>
    %103 = addi %97, %101 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i32>
    %104 = cmpi ult, %103, %99 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %104, %103 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %104, %result_38 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %trueResult_44, %falseResult_45 = cond_br %104, %102 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %105 = mux %index_47 [%falseResult_45, %trueResult_84] {handshake.bb = 7 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%falseResult_43, %trueResult_86]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %106 = br %105 {handshake.bb = 7 : ui32, handshake.name = "br16"} : <i32>
    %107 = br %result_46 {handshake.bb = 7 : ui32, handshake.name = "br17"} : <>
    %108 = mux %index_49 [%106, %trueResult_76] {handshake.bb = 8 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %109 = mux %index_49 [%106, %trueResult_78] {handshake.bb = 8 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_48, %index_49 = control_merge [%107, %trueResult_80]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %110 = constant %result_48 {handshake.bb = 8 : ui32, handshake.name = "constant32", value = 0.000000e+00 : f32} : <>, <f32>
    %111 = constant %result_48 {handshake.bb = 8 : ui32, handshake.name = "constant33", value = 0 : i32} : <>, <i32>
    %112 = extui %109 {handshake.bb = 8 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %113 = extui %108 {handshake.bb = 8 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %114 = br %110 {handshake.bb = 8 : ui32, handshake.name = "br18"} : <f32>
    %115 = br %111 {handshake.bb = 8 : ui32, handshake.name = "br19"} : <i32>
    %116 = br %109 {handshake.bb = 8 : ui32, handshake.name = "br20"} : <i32>
    %117 = br %108 {handshake.bb = 8 : ui32, handshake.name = "br21"} : <i32>
    %118 = br %112 {handshake.bb = 8 : ui32, handshake.name = "br22"} : <i64>
    %119 = br %113 {handshake.bb = 8 : ui32, handshake.name = "br23"} : <i64>
    %120 = br %result_48 {handshake.bb = 8 : ui32, handshake.name = "br24"} : <>
    %121 = mux %index_51 [%114, %trueResult_56] {handshake.bb = 9 : ui32, handshake.name = "mux12"} : <i1>, [<f32>, <f32>] to <f32>
    %122 = mux %index_51 [%115, %trueResult_58] {handshake.bb = 9 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %123 = mux %index_51 [%116, %trueResult_60] {handshake.bb = 9 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %124 = mux %index_51 [%117, %trueResult_62] {handshake.bb = 9 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %125 = mux %index_51 [%118, %trueResult_64] {handshake.bb = 9 : ui32, handshake.name = "mux16"} : <i1>, [<i64>, <i64>] to <i64>
    %126 = mux %index_51 [%119, %trueResult_66] {handshake.bb = 9 : ui32, handshake.name = "mux17"} : <i1>, [<i64>, <i64>] to <i64>
    %result_50, %index_51 = control_merge [%120, %trueResult_68]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>, <>] to <>, <i1>
    %127 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %128 = constant %127 {handshake.bb = 9 : ui32, handshake.name = "constant34", value = 30 : i32} : <>, <i32>
    %129 = source {handshake.bb = 9 : ui32, handshake.name = "source18"} : <>
    %130 = constant %129 {handshake.bb = 9 : ui32, handshake.name = "constant35", value = 1 : i32} : <>, <i32>
    %131 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %132 = constant %131 {handshake.bb = 9 : ui32, handshake.name = "constant36", value = 4 : i64} : <>, <i64>
    %133 = source {handshake.bb = 9 : ui32, handshake.name = "source20"} : <>
    %134 = constant %133 {handshake.bb = 9 : ui32, handshake.name = "constant37", value = 3 : i64} : <>, <i64>
    %135 = source {handshake.bb = 9 : ui32, handshake.name = "source21"} : <>
    %136 = constant %135 {handshake.bb = 9 : ui32, handshake.name = "constant38", value = 2 : i64} : <>, <i64>
    %137 = source {handshake.bb = 9 : ui32, handshake.name = "source22"} : <>
    %138 = constant %137 {handshake.bb = 9 : ui32, handshake.name = "constant39", value = 1 : i64} : <>, <i64>
    %139 = extui %122 {handshake.bb = 9 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %140 = shli %139, %138 {handshake.bb = 9 : ui32, handshake.name = "shli8"} : <i64>
    %141 = shli %139, %136 {handshake.bb = 9 : ui32, handshake.name = "shli9"} : <i64>
    %142 = addi %140, %141 {handshake.bb = 9 : ui32, handshake.name = "addi19"} : <i64>
    %143 = shli %139, %134 {handshake.bb = 9 : ui32, handshake.name = "shli10"} : <i64>
    %144 = shli %139, %132 {handshake.bb = 9 : ui32, handshake.name = "shli11"} : <i64>
    %145 = addi %143, %144 {handshake.bb = 9 : ui32, handshake.name = "addi20"} : <i64>
    %146 = addi %142, %145 {handshake.bb = 9 : ui32, handshake.name = "addi21"} : <i64>
    %147 = addi %146, %125 {handshake.bb = 9 : ui32, handshake.name = "addi6"} : <i64>
    %148 = trunci %147 {handshake.bb = 9 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_52, %dataResult_53 = load[%148] %2#1 {handshake.bb = 9 : ui32, handshake.name = "load5"} : <i32>, <f32>, <i32>, <f32>
    %149 = extui %122 {handshake.bb = 9 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %150 = shli %149, %138 {handshake.bb = 9 : ui32, handshake.name = "shli12"} : <i64>
    %151 = shli %149, %136 {handshake.bb = 9 : ui32, handshake.name = "shli13"} : <i64>
    %152 = addi %150, %151 {handshake.bb = 9 : ui32, handshake.name = "addi22"} : <i64>
    %153 = shli %149, %134 {handshake.bb = 9 : ui32, handshake.name = "shli14"} : <i64>
    %154 = shli %149, %132 {handshake.bb = 9 : ui32, handshake.name = "shli15"} : <i64>
    %155 = addi %153, %154 {handshake.bb = 9 : ui32, handshake.name = "addi23"} : <i64>
    %156 = addi %152, %155 {handshake.bb = 9 : ui32, handshake.name = "addi24"} : <i64>
    %157 = addi %156, %126 {handshake.bb = 9 : ui32, handshake.name = "addi7"} : <i64>
    %158 = trunci %157 {handshake.bb = 9 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_54, %dataResult_55 = load[%158] %2#2 {handshake.bb = 9 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %159 = mulf %dataResult_53, %dataResult_55 {fastmath = #arith.fastmath<none>, handshake.bb = 9 : ui32, handshake.name = "mulf0"} : <f32>
    %160 = addf %121, %159 {fastmath = #arith.fastmath<none>, handshake.bb = 9 : ui32, handshake.name = "addf1"} : <f32>
    %161 = addi %122, %130 {handshake.bb = 9 : ui32, handshake.name = "addi8"} : <i32>
    %162 = cmpi ult, %161, %128 {handshake.bb = 9 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_56, %falseResult_57 = cond_br %162, %160 {handshake.bb = 9 : ui32, handshake.name = "cond_br22"} : <i1>, <f32>
    %trueResult_58, %falseResult_59 = cond_br %162, %161 {handshake.bb = 9 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_60, %falseResult_61 = cond_br %162, %123 {handshake.bb = 9 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %162, %124 {handshake.bb = 9 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %162, %125 {handshake.bb = 9 : ui32, handshake.name = "cond_br26"} : <i1>, <i64>
    %trueResult_66, %falseResult_67 = cond_br %162, %126 {handshake.bb = 9 : ui32, handshake.name = "cond_br27"} : <i1>, <i64>
    %trueResult_68, %falseResult_69 = cond_br %162, %result_50 {handshake.bb = 9 : ui32, handshake.name = "cond_br28"} : <i1>, <>
    %163 = merge %falseResult_57 {handshake.bb = 10 : ui32, handshake.name = "merge3"} : <f32>
    %164 = merge %falseResult_61 {handshake.bb = 10 : ui32, handshake.name = "merge4"} : <i32>
    %165 = merge %falseResult_63 {handshake.bb = 10 : ui32, handshake.name = "merge5"} : <i32>
    %result_70, %index_71 = control_merge [%falseResult_69]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %166 = source {handshake.bb = 10 : ui32, handshake.name = "source23"} : <>
    %167 = constant %166 {handshake.bb = 10 : ui32, handshake.name = "constant40", value = 30 : i32} : <>, <i32>
    %168 = source {handshake.bb = 10 : ui32, handshake.name = "source24"} : <>
    %169 = constant %168 {handshake.bb = 10 : ui32, handshake.name = "constant41", value = 1 : i32} : <>, <i32>
    %170 = source {handshake.bb = 10 : ui32, handshake.name = "source25"} : <>
    %171 = constant %170 {handshake.bb = 10 : ui32, handshake.name = "constant42", value = 4 : i64} : <>, <i64>
    %172 = source {handshake.bb = 10 : ui32, handshake.name = "source26"} : <>
    %173 = constant %172 {handshake.bb = 10 : ui32, handshake.name = "constant43", value = 3 : i64} : <>, <i64>
    %174 = source {handshake.bb = 10 : ui32, handshake.name = "source27"} : <>
    %175 = constant %174 {handshake.bb = 10 : ui32, handshake.name = "constant44", value = 2 : i64} : <>, <i64>
    %176 = source {handshake.bb = 10 : ui32, handshake.name = "source28"} : <>
    %177 = constant %176 {handshake.bb = 10 : ui32, handshake.name = "constant45", value = 1 : i64} : <>, <i64>
    %178 = extui %164 {handshake.bb = 10 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %179 = extui %165 {handshake.bb = 10 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %180 = shli %178, %177 {handshake.bb = 10 : ui32, handshake.name = "shli16"} : <i64>
    %181 = shli %178, %175 {handshake.bb = 10 : ui32, handshake.name = "shli17"} : <i64>
    %182 = addi %180, %181 {handshake.bb = 10 : ui32, handshake.name = "addi25"} : <i64>
    %183 = shli %178, %173 {handshake.bb = 10 : ui32, handshake.name = "shli18"} : <i64>
    %184 = shli %178, %171 {handshake.bb = 10 : ui32, handshake.name = "shli19"} : <i64>
    %185 = addi %183, %184 {handshake.bb = 10 : ui32, handshake.name = "addi26"} : <i64>
    %186 = addi %182, %185 {handshake.bb = 10 : ui32, handshake.name = "addi27"} : <i64>
    %187 = addi %186, %179 {handshake.bb = 10 : ui32, handshake.name = "addi9"} : <i64>
    %188 = trunci %187 {handshake.bb = 10 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_72, %dataResult_73 = store[%188] %163 {handshake.bb = 10 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : <i32>, <f32>, <i32>, <f32>
    %189 = extui %165 {handshake.bb = 10 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %190 = extui %164 {handshake.bb = 10 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %191 = shli %189, %177 {handshake.bb = 10 : ui32, handshake.name = "shli20"} : <i64>
    %192 = shli %189, %175 {handshake.bb = 10 : ui32, handshake.name = "shli21"} : <i64>
    %193 = addi %191, %192 {handshake.bb = 10 : ui32, handshake.name = "addi28"} : <i64>
    %194 = shli %189, %173 {handshake.bb = 10 : ui32, handshake.name = "shli22"} : <i64>
    %195 = shli %189, %171 {handshake.bb = 10 : ui32, handshake.name = "shli23"} : <i64>
    %196 = addi %194, %195 {handshake.bb = 10 : ui32, handshake.name = "addi29"} : <i64>
    %197 = addi %193, %196 {handshake.bb = 10 : ui32, handshake.name = "addi30"} : <i64>
    %198 = addi %197, %190 {handshake.bb = 10 : ui32, handshake.name = "addi10"} : <i64>
    %199 = trunci %198 {handshake.bb = 10 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_74, %dataResult_75 = store[%199] %163 {handshake.bb = 10 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : <i32>, <f32>, <i32>, <f32>
    %200 = addi %165, %169 {handshake.bb = 10 : ui32, handshake.name = "addi11"} : <i32>
    %201 = cmpi ult, %200, %167 {handshake.bb = 10 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_76, %falseResult_77 = cond_br %201, %200 {handshake.bb = 10 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_78, %falseResult_79 = cond_br %201, %164 {handshake.bb = 10 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_80, %falseResult_81 = cond_br %201, %result_70 {handshake.bb = 10 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %202 = merge %falseResult_79 {handshake.bb = 11 : ui32, handshake.name = "merge6"} : <i32>
    %result_82, %index_83 = control_merge [%falseResult_81]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    %203 = source {handshake.bb = 11 : ui32, handshake.name = "source29"} : <>
    %204 = constant %203 {handshake.bb = 11 : ui32, handshake.name = "constant46", value = 30 : i32} : <>, <i32>
    %205 = source {handshake.bb = 11 : ui32, handshake.name = "source30"} : <>
    %206 = constant %205 {handshake.bb = 11 : ui32, handshake.name = "constant47", value = 1 : i32} : <>, <i32>
    %207 = addi %202, %206 {handshake.bb = 11 : ui32, handshake.name = "addi12"} : <i32>
    %208 = cmpi ult, %207, %204 {handshake.bb = 11 : ui32, handshake.name = "cmpi6"} : <i32>
    %trueResult_84, %falseResult_85 = cond_br %208, %207 {handshake.bb = 11 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %trueResult_86, %falseResult_87 = cond_br %208, %result_82 {handshake.bb = 11 : ui32, handshake.name = "cond_br33"} : <i1>, <>
    %result_88, %index_89 = control_merge [%falseResult_87]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>] to <>, <i1>
    end {handshake.bb = 12 : ui32, handshake.name = "end0"} %memEnd, %1, %0#1, %arg6 : <>, <>, <>, <>
  }
}

