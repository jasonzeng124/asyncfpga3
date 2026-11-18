module {
  handshake.func @countloop(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "n", "start"], resNames = ["out0", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:4 = fork [4] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %8:2 = fork [2] %7 {handshake.bb = 0 : ui32, handshake.name = "fork3"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %4#3, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %9 = mux %16#0 [%8#0, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %11 = mux %16#1 [%8#1, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %16#2 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %rd0s = source {handshake.bb = 0 : ui32, handshake.name = "sourcerd0"} : <>
    %rd0c = constant %rd0s {handshake.bb = 0 : ui32, handshake.name = "constantrd0", value = -1 : i32} : <>, <i32>
    %rd0d = addi %trueResult_2, %rd0c {handshake.bb = 0 : ui32, handshake.name = "addird0"} : <i32>
    %14 = mux %16#3 [%rd0d, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %19 = addi %11, %10#1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %20 = xori %19, %13#1 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %rd0f:2 = fork [2] %10#0 {handshake.bb = 1 : ui32, handshake.name = "forkrd0"} : <i32>
    %21 = addi %rd0f#0, %18 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %rd0i:2 = fork [2] %rd0f#1 {handshake.bb = 1 : ui32, handshake.name = "forkrd1"} : <i32>
    %rd0m:2 = fork [2] %15#1 {handshake.bb = 1 : ui32, handshake.name = "forkrd2"} : <i32>
    %rd0lt = cmpi slt, %rd0i#0, %rd0m#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %rd0s1 = source {handshake.bb = 1 : ui32, handshake.name = "sourcerd1"} : <>
    %rd0k1 = constant %rd0s1 {handshake.bb = 1 : ui32, handshake.name = "constantrd1", value = 2147483647 : i32} : <>, <i32>
    %rd0s2 = source {handshake.bb = 1 : ui32, handshake.name = "sourcerd2"} : <>
    %rd0k2 = constant %rd0s2 {handshake.bb = 1 : ui32, handshake.name = "constantrd2", value = 2147483647 : i32} : <>, <i32>
    %rd0ei = cmpi eq, %rd0i#1, %rd0k1 {handshake.bb = 1 : ui32, handshake.name = "cmpird1"} : <i32>
    %rd0em = cmpi eq, %rd0m#1, %rd0k2 {handshake.bb = 1 : ui32, handshake.name = "cmpird2"} : <i32>
    %rd0x = xori %rd0lt, %rd0ei {handshake.bb = 1 : ui32, handshake.name = "xorird0"} : <i1>
    %23 = xori %rd0x, %rd0em {handshake.bb = 1 : ui32, handshake.name = "xorird1"} : <i1>
    %24:5 = fork [5] %23 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %24#4, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_7 {handshake.name = "sink2"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %24#3, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %24#2, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink3"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %24#1, %15#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink4"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %24#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %25 = mux %index_17 [%6, %falseResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_16, %index_17 = control_merge [%falseResult_5, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %result_16 {handshake.name = "sink5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %25, %0#1 : <i32>, <>
  }
}

