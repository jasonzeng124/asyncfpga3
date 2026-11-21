module {
  handshake.func @test_memory_5(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:3 = lsq[%arg0 : memref<4xi32>] (%arg2, %18#0, %addressResult, %addressResult_4, %addressResult_6, %dataResult_7, %result_14)  {groupSizes = [3 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = -2 : i2} : <>, <i2>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink0"} : <i2>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i2> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %8 = mux %17#0 [%7, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:4 = fork [4] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %11 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i2} : <>, <i2>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %13 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -2 : i2} : <>, <i2>
    %14 = trunci %9#2 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i2>
    %15 = mux %17#1 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %17:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %18:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 5 : i32} : <>, <i32>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %25 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i2>
    %addressResult, %dataResult = load[%25] %2#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %26 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i2>
    %addressResult_4, %dataResult_5 = load[%26] %2#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %27 = addi %dataResult, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %28 = addi %27, %22 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_6, %dataResult_7 = store[%14] %28 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %29 = addi %9#3, %20 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %31 = cmpi slt, %30#1, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %32:3 = fork [3] %31 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %32#2, %30#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink2"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %32#1, %16#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink3"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %32#0, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_14, %index_15 = control_merge [%falseResult_3, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_15 {handshake.name = "sink4"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %2#2, %0#1 : <>, <>
  }
}

