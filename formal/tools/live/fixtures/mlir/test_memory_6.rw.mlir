module {
  handshake.func @test_memory_6(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:3 = lsq[%arg0 : memref<4xi32>] (%arg2, %20#0, %addressResult, %addressResult_4, %addressResult_6, %dataResult_7, %addressResult_8, %dataResult_9, %result_16)  {groupSizes = [4 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
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
    %8 = mux %19#0 [%7, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:5 = fork [5] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %11 = constant %28#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i2} : <>, <i2>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %13 = constant %26 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -2 : i2} : <>, <i2>
    %14 = trunci %9#2 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i2>
    %15 = constant %28#1 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = -1 : i2} : <>, <i2>
    %16 = trunci %9#3 {handshake.bb = 1 : ui32, handshake.name = "trunci3"} : <i32> to <i2>
    %17 = mux %19#1 [%trueResult_0, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %19:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %20:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %23 = constant %20#2 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 5 : i32} : <>, <i32>
    %26 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %27 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %29 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i2>
    %addressResult, %dataResult = load[%29] %2#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %30 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i2>
    %addressResult_4, %dataResult_5 = load[%30] %2#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %31 = addi %dataResult, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %32 = addi %31, %25 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_6, %dataResult_7 = store[%16] %32 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %33 = addi %14, %15 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i2>
    %addressResult_8, %dataResult_9 = store[%33] %23 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %34 = addi %9#4, %22 {handshake.bb = 1 : ui32, handshake.name = "addi5"} : <i32>
    %35:2 = fork [2] %34 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %36 = cmpi slt, %35#1, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %37:3 = fork [3] %36 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_10, %falseResult_11 = cond_br %37#2, %35#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %37#1, %18#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink3"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %37#0, %20#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_3, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_17 {handshake.name = "sink4"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %2#2, %0#1 : <>, <>
  }
}

