module {
  handshake.func @simpleLoad(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "in0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<4xi32>] %arg2 (%addressResult) %arg3 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %addressResult, %dataResult = load[%arg1] %outputs {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %dataResult, %memEnd, %arg3 : <i32>, <>, <>
  }
}


// -----
module {
  handshake.func @ifThenElse(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i1>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["in0", "in1", "start"], resNames = ["out0", "end"]} {
    %trueResult, %falseResult = cond_br %arg1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %0 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %1 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 1 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %3 = addi %0, %2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %4 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br0"} : <i32>
    %5 = br %result {handshake.bb = 1 : ui32, handshake.name = "br1"} : <>
    %6 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_2, %index_3 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %7 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 2 : i32} : <>, <i32>
    %9 = addi %6, %8 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %10 = br %9 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %11 = br %result_2 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <>
    %12 = mux %index_5 [%4, %10] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result_4, %index_5 = control_merge [%5, %11]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %12, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @multipleReturns(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i1>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["in0", "in1", "start"], resNames = ["out0", "end"]} {
    %trueResult, %falseResult = cond_br %arg1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %0 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %1 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 1 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %3 = addi %0, %2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %4 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_2, %index_3 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %5 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 2 : i32} : <>, <i32>
    %7 = addi %4, %6 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %8 = merge %3, %7 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %8, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @simpleLoop(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["in0", "start"], resNames = ["end"]} {
    %0 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <i32>
    %3 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %4 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%2, %14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %15] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%4, %16] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %17]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = cmpi slt, %6, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %9, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %9, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %9, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %9, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %10 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %11 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %12 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_6, %index_7 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %13 = addi %12, %11 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %14 = br %13 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %15 = br %10 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %16 = br %11 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %17 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %result_8, %index_9 = control_merge [%falseResult_5]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %arg1 : <>
  }
}

