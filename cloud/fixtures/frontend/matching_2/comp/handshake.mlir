module {
  handshake.func @matching_2(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["edges", "vertices", "num_edges", "edges_start", "vertices_start", "start"], resNames = ["edges_end", "vertices_end", "end"]} {
    %0:3 = lsq[%arg1 : memref<1000xf32>] (%arg4, %result, %addressResult_4, %result_16, %addressResult_20, %result_32, %addressResult_34, %dataResult_35, %addressResult_36, %dataResult_37, %result_46)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult, %addressResult_18) %result_46 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg2, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0.000000e+00 : f32} : <>, <f32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = shli %3, %8 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %10 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%11] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %12 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_4, %dataResult_5 = load[%12] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %13 = cmpf olt, %dataResult_5, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult_6, %falseResult_7 = cond_br %13, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %13, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %13, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %13, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %13, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %14 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %15 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %16 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %17 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_16, %index_17 = control_merge [%trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0.000000e+00 : f32} : <>, <f32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %22 = ori %16, %21 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %23 = extui %22 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %24 = trunci %23 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = load[%24] %outputs#1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %25 = trunci %dataResult_19 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_20, %dataResult_21 = load[%25] %0#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %26 = cmpf olt, %dataResult_21, %19 {handshake.bb = 2 : ui32, handshake.name = "cmpf1"} : <f32>
    %trueResult_22, %falseResult_23 = cond_br %26, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %26, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %26, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %26, %dataResult_19 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %26, %result_16 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %27 = merge %trueResult_22 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %28 = merge %trueResult_24 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %29 = merge %trueResult_26 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %30 = merge %trueResult_28 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i32>
    %result_32, %index_33 = control_merge [%trueResult_30]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %31 = sitofp %30 {handshake.bb = 3 : ui32, handshake.name = "sitofp0"} : <i32> to <f32>
    %32 = trunci %29 {handshake.bb = 3 : ui32, handshake.name = "index_cast4"} : <i32> to <i32>
    %addressResult_34, %dataResult_35 = store[%32] %31 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <f32>, <i32>, <f32>
    %33 = sitofp %29 {handshake.bb = 3 : ui32, handshake.name = "sitofp1"} : <i32> to <f32>
    %34 = trunci %30 {handshake.bb = 3 : ui32, handshake.name = "index_cast5"} : <i32> to <i32>
    %addressResult_36, %dataResult_37 = store[%34] %33 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <f32>, <i32>, <f32>
    %35 = br %27 {handshake.bb = 3 : ui32, handshake.name = "br1"} : <i32>
    %36 = br %28 {handshake.bb = 3 : ui32, handshake.name = "br2"} : <i32>
    %37 = br %result_32 {handshake.bb = 3 : ui32, handshake.name = "br3"} : <>
    %38 = mux %index_39 [%falseResult_7, %falseResult_23, %35] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %39 = mux %index_39 [%falseResult_9, %falseResult_25, %36] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%falseResult_15, %falseResult_31, %37]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %40 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %41 = constant %40 {handshake.bb = 4 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %42 = addi %39, %41 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %43 = cmpi slt, %42, %38 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %43, %42 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %43, %38 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %43, %result_38 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_3, %falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %memEnd, %0#2, %arg5 : <>, <>, <>
  }
}

