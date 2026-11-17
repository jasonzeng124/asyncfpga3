module {
  handshake.func @path_profiling(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "var", "a_start", "b_start", "var_start", "start"], resNames = ["a_end", "b_end", "var_end", "end"]} {
    %outputs:2, %memEnd = mem_controller[%arg2 : memref<20xi32>] %arg5 (%addressResult, %addressResult_12) %result_32 {connectedBlocks = [1 : i32, 4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0 = lsq[%arg1 : memref<20xi32>] (%arg4, %result_18, %addressResult_20, %dataResult_21, %result_22, %addressResult_24, %dataResult_25, %result_32)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> !handshake.control<>
    %1 = lsq[%arg0 : memref<20xi32>] (%arg3, %result_2, %addressResult_4, %dataResult_5, %result_6, %addressResult_8, %dataResult_9, %result_32)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> !handshake.control<>
    %2 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %4 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %5 = mux %index [%3, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %10 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%11] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %12 = andi %dataResult, %7 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %13 = cmpi eq, %12, %9 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %13, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %13, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %14 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_2, %index_3 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %15 = constant %result_2 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 2 : i32} : <>, <i32>
    %16 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %17 = trunci %16 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = store[%17] %15 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %18 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %19 = br %result_2 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <>
    %20 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_6, %index_7 = control_merge [%falseResult_1]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %21 = constant %result_6 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 3 : i32} : <>, <i32>
    %22 = extui %20 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %23 = trunci %22 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = store[%23] %21 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %24 = br %20 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <i32>
    %25 = br %result_6 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <>
    %26 = mux %index_11 [%18, %24] {handshake.bb = 4 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%19, %25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %27 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %28 = constant %27 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %29 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %30 = constant %29 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %31 = extui %26 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %32 = trunci %31 {handshake.bb = 4 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%32] %outputs#1 {handshake.bb = 4 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %33 = remsi %dataResult_13, %28 {handshake.bb = 4 : ui32, handshake.name = "remsi0"} : <i32>
    %34 = cmpi eq, %33, %30 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %34, %26 {handshake.bb = 4 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %34, %result_10 {handshake.bb = 4 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %35 = merge %trueResult_14 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %result_18, %index_19 = control_merge [%trueResult_16]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %36 = constant %result_18 {handshake.bb = 5 : ui32, handshake.name = "constant11", value = 2 : i32} : <>, <i32>
    %37 = extui %35 {handshake.bb = 5 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %38 = trunci %37 {handshake.bb = 5 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_20, %dataResult_21 = store[%38] %36 {handshake.bb = 5 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %39 = br %35 {handshake.bb = 5 : ui32, handshake.name = "br11"} : <i32>
    %40 = br %result_18 {handshake.bb = 5 : ui32, handshake.name = "br12"} : <>
    %41 = merge %falseResult_15 {handshake.bb = 6 : ui32, handshake.name = "merge3"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_17]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %42 = constant %result_22 {handshake.bb = 6 : ui32, handshake.name = "constant12", value = 3 : i32} : <>, <i32>
    %43 = extui %41 {handshake.bb = 6 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %44 = trunci %43 {handshake.bb = 6 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = store[%44] %42 {handshake.bb = 6 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %45 = br %41 {handshake.bb = 6 : ui32, handshake.name = "br13"} : <i32>
    %46 = br %result_22 {handshake.bb = 6 : ui32, handshake.name = "br14"} : <>
    %47 = mux %index_27 [%39, %45] {handshake.bb = 7 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%40, %46]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %48 = source {handshake.bb = 7 : ui32, handshake.name = "source4"} : <>
    %49 = constant %48 {handshake.bb = 7 : ui32, handshake.name = "constant13", value = 20 : i32} : <>, <i32>
    %50 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %51 = constant %50 {handshake.bb = 7 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %52 = addi %47, %51 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i32>
    %53 = cmpi ult, %52, %49 {handshake.bb = 7 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %53, %52 {handshake.bb = 7 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %53, %result_26 {handshake.bb = 7 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_32, %index_33 = control_merge [%falseResult_31]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    end {handshake.bb = 8 : ui32, handshake.name = "end0"} %1, %0, %memEnd, %arg6 : <>, <>, <>, <>
  }
}

