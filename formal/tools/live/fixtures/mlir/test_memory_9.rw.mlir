module {
  handshake.func @test_memory_9(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %16#0, %addressResult, %addressResult_4, %dataResult_5, %result_12)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %8 = mux %15#0 [%7, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %11 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i2} : <>, <i2>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %13 = mux %15#1 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14:2 = fork [2] %13 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %15:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %16:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %21 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 2 : i32} : <>, <i32>
    %22 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i2>
    %addressResult, %dataResult = load[%22] %2#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %23:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %24 = shli %23#0, %21 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %25 = addi %23#1, %24 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %addressResult_4, %dataResult_5 = store[%12] %25 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i2>, <i32>, <i2>, <i32>
    %26 = addi %9#2, %19 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %27:2 = fork [2] %26 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %28 = cmpi slt, %27#1, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %29:3 = fork [3] %28 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %29#2, %27#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %29#1, %14#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %29#0, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_12, %index_13 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_13 {handshake.name = "sink4"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %2#1, %0#1 : <>, <>
  }
}

