module {
  handshake.func @matching(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["edges", "vertices", "num_edges", "edges_start", "vertices_start", "start"], resNames = ["out0", "edges_end", "vertices_end", "end"]} {
    %0:3 = lsq[%arg1 : memref<1000xi32>] (%arg4, %result, %addressResult_6, %result_20, %addressResult_24, %result_38, %addressResult_40, %dataResult_41, %addressResult_42, %dataResult_43, %result_54)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult, %addressResult_22) %result_54 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0.000000e+00 : f32} : <>, <f32>
    %3 = cmpi sgt, %arg2, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %3, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %3, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %3, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %4 = mux %index [%trueResult, %trueResult_46] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %5 = mux %index [%trueResult_0, %trueResult_48] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_2, %trueResult_50] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_52]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %11 = shli %5, %8 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %12 = extui %11 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %13 = trunci %12 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%13] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %14 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_6, %dataResult_7 = load[%14] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %15 = cmpi slt, %dataResult_7, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %15, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %15, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %15, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %15, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %15, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %16 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %17 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %18 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %19 = merge %trueResult_14 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %20 = merge %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %25 = ori %19, %22 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %26 = extui %25 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %27 = trunci %26 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_22, %dataResult_23 = load[%27] %outputs#1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %28 = trunci %dataResult_23 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_24, %dataResult_25 = load[%28] %0#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %29 = cmpi slt, %dataResult_25, %24 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %29, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %29, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <f32>
    %trueResult_30, %falseResult_31 = cond_br %29, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %29, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %29, %dataResult_23 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %29, %result_20 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %30 = merge %trueResult_26 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %31 = merge %trueResult_28 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <f32>
    %32 = merge %trueResult_30 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i32>
    %33 = merge %trueResult_32 {handshake.bb = 3 : ui32, handshake.name = "merge8"} : <i32>
    %34 = merge %trueResult_34 {handshake.bb = 3 : ui32, handshake.name = "merge9"} : <i32>
    %result_38, %index_39 = control_merge [%trueResult_36]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %35 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %36 = constant %35 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1.000000e+00 : f32} : <>, <f32>
    %37 = trunci %33 {handshake.bb = 3 : ui32, handshake.name = "index_cast4"} : <i32> to <i32>
    %addressResult_40, %dataResult_41 = store[%37] %34 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %38 = trunci %34 {handshake.bb = 3 : ui32, handshake.name = "index_cast5"} : <i32> to <i32>
    %addressResult_42, %dataResult_43 = store[%38] %33 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %39 = addf %31, %36 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %40 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <f32>
    %41 = br %30 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %42 = br %32 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <i32>
    %43 = br %result_38 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <>
    %44 = mux %index_45 [%falseResult_11, %falseResult_29, %40] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i2>, [<f32>, <f32>, <f32>] to <f32>
    %45 = mux %index_45 [%falseResult_9, %falseResult_27, %41] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %46 = mux %index_45 [%falseResult_13, %falseResult_31, %42] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_44, %index_45 = control_merge [%falseResult_19, %falseResult_37, %43]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %47 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %48 = constant %47 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %49 = addi %46, %48 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %50 = cmpi slt, %49, %45 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_46, %falseResult_47 = cond_br %50, %44 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <f32>
    %trueResult_48, %falseResult_49 = cond_br %50, %49 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_50, %falseResult_51 = cond_br %50, %45 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %50, %result_44 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %51 = mux %index_55 [%falseResult, %falseResult_47] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %result_54, %index_55 = control_merge [%falseResult_5, %falseResult_53]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %51, %memEnd, %0#2, %arg5 : <f32>, <>, <>, <>
  }
}

