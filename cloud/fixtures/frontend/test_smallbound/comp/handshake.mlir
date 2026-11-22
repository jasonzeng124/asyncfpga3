module {
  handshake.func @test_smallbound(%arg0: memref<4xi32>, %arg1: memref<2xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "y", "x_start", "y_start", "start"], resNames = ["x_end", "y_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<2xi32>] %arg3 (%addressResult) %result_20 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %result_0, %addressResult_2, %addressResult_4, %dataResult_5, %result_20)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %8 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %9 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i64>
    %11 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %12 = br %result {handshake.bb = 1 : ui32, handshake.name = "br8"} : <>
    %13 = mux %index_1 [%8, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_1 [%9, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_1 [%10, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %16 = mux %index_1 [%11, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_0, %index_1 = control_merge [%12, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 2 : i32} : <>, <i32>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %21 = constant %result_0 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i64} : <>, <i64>
    %24 = trunci %15 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%24] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_2, %dataResult_3 = load[%21] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %25 = addi %dataResult, %dataResult_3 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %26 = extui %13 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %27 = shli %16, %23 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %28 = addi %27, %26 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = store[%29] %25 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %30 = addi %13, %20 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %31 = cmpi ult, %30, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %31, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %31, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %31, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i64>
    %trueResult_10, %falseResult_11 = cond_br %31, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_12, %falseResult_13 = cond_br %31, %result_0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %32 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %34 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 2 : i32} : <>, <i32>
    %35 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %36 = constant %35 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %37 = addi %32, %36 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %38 = cmpi ult, %37, %34 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %38, %37 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %38, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg4 : <>, <>, <>
  }
}

