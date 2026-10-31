module {
  handshake.func @test_loop_free(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "d", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg4 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %3 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %4 = merge %trueResult_0 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %5 = merge %trueResult_2 {handshake.bb = 1 : ui32, handshake.name = "merge2"} : <i32>
    %result, %index = control_merge [%trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %6 = addi %3, %4 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %7 = addi %6, %5 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %8 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %9 = br %result {handshake.bb = 1 : ui32, handshake.name = "br3"} : <>
    %10 = merge %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %11 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %12 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge5"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %15 = cmpi slt, %11, %14 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %16 = addi %10, %12 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %17 = select %15[%16, %10] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %18 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %19 = br %result_8 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %20 = mux %index_11 [%8, %18] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%9, %19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %20, %arg4 : <i32>, <>
  }
}

