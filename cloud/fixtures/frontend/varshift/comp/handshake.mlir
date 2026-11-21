module {
  handshake.func @varshift(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1540483477 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 31 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 7 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 27 : i32} : <>, <i32>
    %15 = shrui %4, %14 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i32>
    %16 = andi %15, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %17 = shli %4, %16 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %18 = shrui %5, %15 {handshake.bb = 1 : ui32, handshake.name = "shrui1"} : <i32>
    %19 = xori %17, %18 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %20 = xori %15, %10 {handshake.bb = 1 : ui32, handshake.name = "xori1"} : <i32>
    %21 = shrsi %4, %20 {handshake.bb = 1 : ui32, handshake.name = "shrsi0"} : <i32>
    %22 = xori %19, %21 {handshake.bb = 1 : ui32, handshake.name = "xori2"} : <i32>
    %23 = xori %22, %3 {handshake.bb = 1 : ui32, handshake.name = "xori3"} : <i32>
    %24 = addi %3, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %25 = cmpi slt, %24, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %25, %24 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %25, %23 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %25, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %25, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %25, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %26 = mux %index_19 [%falseResult_1, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_18, %index_19 = control_merge [%falseResult_7, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %26, %arg2 : <i32>, <>
  }
}

