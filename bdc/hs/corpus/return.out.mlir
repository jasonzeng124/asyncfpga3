module {
  handshake.func @simpleReturn(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["in0", "start"], resNames = ["out0", "end"]} {
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %arg0, %arg1 : <i32>, <>
  }
}


// -----
module {
  handshake.func @retunMultipleValues(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i1>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i1>, !handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["in0", "in1", "in2", "start"], resNames = ["out0", "out1", "out2", "end"]} {
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %arg0, %arg1, %arg2, %arg3 : <i32>, <i1>, <i32>, <>
  }
}


// -----
module {
  handshake.func @multipleReturns(%arg0: !handshake.channel<i1>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["in0", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %trueResult, %falseResult = cond_br %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %2 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %3 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %4 = merge %2, %3 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %4, %arg1 : <i32>, <>
  }
}


// -----
module {
  handshake.func @memoryConnect(%arg0: !handshake.channel<i1>, %arg1: memref<4xi32>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["in0", "mem0", "mem1", "mem0_start", "mem1_start", "start"], resNames = ["out0", "mem0_end", "mem1_end", "end"]} {
    %0 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %trueResult, %falseResult = cond_br %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %2 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %3 = merge %result, %result_4 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <>
    %4 = merge %falseResult_3 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %5 = merge %2, %4 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %6 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %7 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %5, %6, %7, %arg5 : <i32>, <>, <>, <>
  }
}

