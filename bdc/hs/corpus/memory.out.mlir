module {
  handshake.func @simpleLoadStore(%arg0: !handshake.channel<i32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["in0", "mem0", "mem0_start", "start"], resNames = ["mem0_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<4xi32>] %arg2 (%0, %addressResult, %dataResult, %addressResult_0) %arg3 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%arg0] %1 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = load[%arg0] %outputs {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %memEnd, %arg3 : <>, <>
  }
}


// -----
module {
  handshake.func @storeMulBlocks(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i32>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["in0", "in1", "mem0", "mem0_start", "start"], resNames = ["mem0_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<4xi32>] %arg3 (%0, %addressResult, %dataResult, %4, %addressResult_4, %dataResult_5) %result_6 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %trueResult, %falseResult = cond_br %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg4 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %0 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %1 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %2 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%1] %2 {handshake.bb = 1 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %3 = br %result {handshake.bb = 1 : ui32, handshake.name = "br0"} : <>
    %4 = constant %result_2 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %5 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_2, %index_3 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %6 = constant %result_2 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 2 : i32} : <>, <i32>
    %addressResult_4, %dataResult_5 = store[%5] %6 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %7 = br %result_2 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <>
    %result_6, %index_7 = control_merge [%3, %7]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %memEnd, %arg4 : <>, <>
  }
}


// -----
module {
  handshake.func @forwardLoadToBB(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i32>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["in0", "in1", "mem0", "mem0_start", "start"], resNames = ["mem0_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg2 : memref<4xi32>] %arg3 (%addressResult) %result_2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %addressResult, %dataResult = load[%arg1] %outputs {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %trueResult, %falseResult = cond_br %arg0, %dataResult {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg4 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %0 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %1 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 1 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %3 = addi %0, %2 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %4 = br %result {handshake.bb = 1 : ui32, handshake.name = "br0"} : <>
    %result_2, %index_3 = control_merge [%falseResult_1, %4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %arg4 : <>, <>
  }
}


// -----
module {
  handshake.func @multipleMemories(%arg0: !handshake.channel<i1>, %arg1: memref<4xi32>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["in0", "mem0", "mem1", "mem0_start", "mem1_start", "start"], resNames = ["mem0_end", "mem1_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg2 : memref<4xi32>] %arg4 (%addressResult, %4, %addressResult_12, %dataResult_13) %5 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg1 : memref<4xi32>] %arg3 (%2, %addressResult_6, %dataResult_7, %addressResult_10) %5 {connectedBlocks = [1 : i32, 2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %trueResult, %falseResult = cond_br %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %arg0, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %2 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %3 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %addressResult, %dataResult = load[%3] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_6, %dataResult_7 = store[%3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %4 = constant %result_8 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %5 = merge %result, %result_8 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <>
    %6 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %addressResult_10, %dataResult_11 = load[%6] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_12, %dataResult_13 = store[%6] %dataResult_11 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %arg5 : <>, <>, <>
  }
}

