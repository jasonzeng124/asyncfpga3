module {
  handshake.func @test_loop_free(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "d", "start"], resNames = ["out0", "end"]} {
    %0:2 = fork [2] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:5 = fork [5] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %5#4, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#3, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %5#1, %0#1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_6, %falseResult_7 = cond_br %5#0, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %trueResult_6 {handshake.name = "sink1"} : <i32>
    %6 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %7 = merge %trueResult_0 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %8 = merge %trueResult_2 {handshake.bb = 1 : ui32, handshake.name = "merge2"} : <i32>
    %result, %index = control_merge [%trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    sink %index {handshake.name = "sink2"} : <i1>
    %9 = addi %6, %7 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %10 = addi %9, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %11 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %12 = br %result {handshake.bb = 1 : ui32, handshake.name = "br3"} : <>
    %13 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %14:2 = fork [2] %13 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i32>
    %15 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %16 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge5"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink3"} : <i1>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %19 = cmpi slt, %15, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %20 = addi %14#1, %16 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %21 = select %19[%20, %14#0] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %22 = br %21 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %23 = br %result_8 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %24 = mux %index_11 [%11, %22] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%12, %23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    sink %result_10 {handshake.name = "sink4"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %24, %0#0 : <i32>, <>
  }
}

