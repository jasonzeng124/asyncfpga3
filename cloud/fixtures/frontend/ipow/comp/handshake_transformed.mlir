module {
  handshake.func @ipow(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["b", "e", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:4 = fork [4] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %5#3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = true} : <>, <i1>
    %trueResult_2, %falseResult_3 = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    %7 = extui %falseResult_3 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = extui %trueResult_2 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_4, %falseResult_5 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %9 = mux %17#0 [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:3 = fork [3] %9 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %11 = mux %17#1 [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12:2 = fork [2] %11 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %13 = trunci %12#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %14 = constant %19#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = true} : <>, <i1>
    %15 = mux %17#2 [%8, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %17:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %20 = constant %19#1 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %22:2 = fork [2] %21 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <>
    %23 = constant %22#1 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %24 = andi %13, %14 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %25 = constant %22#0 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %26 = cmpi eq, %24, %25 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i1>
    %27 = muli %16#1, %10#2 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %28 = select %26[%16#0, %27] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %29 = muli %10#0, %10#1 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %30 = shrsi %12#1, %20 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %31:2 = fork [2] %30 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %32 = cmpi sgt, %31#1, %23 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %33:4 = fork [4] %32 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %33#3, %29 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %33#2, %31#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %33#1, %28 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %33#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %34 = mux %index_15 [%7, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_14 {handshake.name = "sink4"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %34, %0#1 : <i32>, <>
  }
}

