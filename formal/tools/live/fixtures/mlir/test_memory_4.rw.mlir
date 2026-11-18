module {
  handshake.func @test_memory_4(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %21#0, %addressResult, %dataResult, %addressResult_4, %result_14)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %4 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %5 = addi %arg1, %3 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %6:2 = fork [2] %5 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %7 = cmpi sgt, %6#1, %4 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %8:3 = fork [3] %7 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %9 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %8#0, %9 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %10 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %11:2 = fork [2] %10 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %8#2, %6#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %8#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %12 = mux %20#0 [%11#0, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %13:3 = fork [3] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %14 = trunci %13#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %15 = constant %23#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i2} : <>, <i2>
    %16 = trunci %13#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %17 = mux %20#1 [%11#1, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %20#2 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %20:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %21:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <>
    %24 = constant %23#1 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%16] %17 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : <i2>, <i32>, <i2>, <i32>
    %25 = addi %14, %15 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i2>
    %addressResult_4, %dataResult_5 = load[%25] %1#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %26 = addi %13#2, %24 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %27:2 = fork [2] %26 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %28 = cmpi slt, %27#1, %19#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %29:4 = fork [4] %28 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %29#3, %27#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %29#2, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %29#1, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink4"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %29#0, %21#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_14, %index_15 = control_merge [%falseResult_3, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_15 {handshake.name = "sink5"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %1#1, %0#1 : <>, <>
  }
}

