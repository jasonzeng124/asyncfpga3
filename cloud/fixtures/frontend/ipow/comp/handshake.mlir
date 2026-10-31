module {
  handshake.func @ipow(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["b", "e", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = cmpi sgt, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %3, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %4 = mux %index [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %11 = andi %5, %8 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %12 = cmpi eq, %11, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %13 = muli %6, %4 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %14 = select %12[%6, %13] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %15 = muli %4, %4 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %16 = shrsi %5, %8 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %17 = cmpi sgt, %16, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %17, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %17, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %18 = mux %index_15 [%falseResult_3, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %18, %arg2 : <i32>, <>
  }
}

