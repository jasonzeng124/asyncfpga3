module {
  handshake.func @collatz(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["n", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = cmpi eq, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %7 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink0"} : <i32>
    %9 = mux %14#0 [%falseResult_3, %falseResult_9] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:4 = fork [4] %9 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %11 = trunci %10#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %12 = constant %17#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = true} : <>, <i1>
    %13 = mux %14#1 [%7, %falseResult_5] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_1, %falseResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %18 = constant %17#1 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %19:5 = fork [5] %18 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %20 = andi %11, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %21 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %22 = cmpi eq, %20, %21 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i1>
    %23 = shrsi %10#3, %19#4 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %24 = shli %10#2, %19#3 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %25 = addi %10#1, %24 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %26 = addi %25, %19#2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %27 = select %22[%23, %26] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %28:2 = fork [2] %27 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %29 = addi %13, %19#1 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %30 = cmpi eq, %28#1, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %31:3 = fork [3] %30 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %31#2, %29 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %31#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %31#0, %28#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %trueResult_8 {handshake.name = "sink1"} : <i32>
    %32 = mux %index_11 [%8, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_0, %trueResult_6]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_10 {handshake.name = "sink2"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %32, %0#1 : <i32>, <>
  }
}

