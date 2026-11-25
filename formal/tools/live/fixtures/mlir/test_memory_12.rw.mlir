module {
  handshake.func @test_memory_12(%arg0: memref<4xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:10 = fork [10] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg0 : memref<4xi32>] %arg1 (%1, %addressResult, %dataResult, %addressResult_0, %dataResult_1, %addressResult_2, %dataResult_3, %24, %addressResult_8, %dataResult_9) %result_16 {connectedBlocks = [0 : i32, 2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>) -> ()
    %1 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant7", value = 3 : i32} : <>, <i32>
    %2 = constant %0#9 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = constant %0#8 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %4 = constant %0#7 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = 2 : i32} : <>, <i32>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant16", value = 0 : i2} : <>, <i2>
    %addressResult, %dataResult = store[%5] %2 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store0"} : <i2>, <i32>, <i2>, <i32>
    %6 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant17", value = 1 : i2} : <>, <i2>
    %addressResult_0, %dataResult_1 = store[%6] %3 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i2>, <i32>, <i2>, <i32>
    %7 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant18", value = -2 : i2} : <>, <i2>
    %addressResult_2, %dataResult_3 = store[%7] %4 {handshake.bb = 0 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %8 = constant %0#2 {handshake.bb = 0 : ui32, handshake.name = "constant19", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %10 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i1> to <i2>
    %11 = br %0#6 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %12 = mux %index [%10, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %14 = trunci %13#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i2> to <i1>
    %15 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant20", value = true} : <>, <i1>
    %result, %index = control_merge [%11, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %18 = andi %14, %15 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %19 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant21", value = false} : <>, <i1>
    %20 = cmpi eq, %18, %19 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i1>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %21#0, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    %trueResult_4, %falseResult_5 = cond_br %21#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %22 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i2>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink0"} : <i1>
    %23:4 = fork [4] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <>
    %24 = constant %23#1 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %25 = constant %23#3 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %26 = constant %23#0 {handshake.bb = 2 : ui32, handshake.name = "constant22", value = -1 : i2} : <>, <i2>
    %addressResult_8, %dataResult_9 = store[%26] %25 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %27 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i2>
    %28 = br %23#2 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %29 = mux %index_11 [%trueResult, %27] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i2>, <i2>] to <i2>
    %30 = extui %29 {handshake.bb = 3 : ui32, handshake.name = "extui1"} : <i2> to <i3>
    %31 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant23", value = 1 : i3} : <>, <i3>
    %result_10, %index_11 = control_merge [%trueResult_4, %28]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %34 = addi %30, %31 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i3>
    %35:2 = fork [2] %34 {handshake.bb = 3 : ui32, handshake.name = "fork4"} : <i3>
    %36 = trunci %35#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i3> to <i2>
    %37 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant24", value = -4 : i3} : <>, <i3>
    %38 = cmpi ult, %35#1, %37 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i3>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %39#0, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i2>
    sink %falseResult_13 {handshake.name = "sink1"} : <i2>
    %trueResult_14, %falseResult_15 = cond_br %39#1, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink2"} : <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %0#5 : <>, <>
  }
}

