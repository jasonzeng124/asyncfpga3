module {
  handshake.func @simpleOneGroupLSQ(%arg0: memref<64xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<64xi32>] (%arg1, %arg2, %addressResult, %addressResult_0, %dataResult_1, %addressResult_2, %dataResult_3, %arg2)  {groupSizes = [3 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %0#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = store[%2] %dataResult {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_2, %dataResult_3 = store[%3] %dataResult {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %dataResult, %0#1, %arg2 : <i32>, <>, <>
  }
}


// -----
module {
  handshake.func @simpleMultiGroupLSQ(%arg0: memref<64xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %0:3 = lsq[%arg0 : memref<64xi32>] (%arg1, %arg2, %addressResult, %addressResult_0, %result, %addressResult_2, %dataResult_3, %addressResult_4, %dataResult_5, %result)  {groupSizes = [2 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %0#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = load[%2] %0#1 {handshake.bb = 0 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %4 = br %dataResult {handshake.bb = 0 : ui32, handshake.name = "br0"} : <i32>
    %5 = br %dataResult_1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %6 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %7 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %8 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %9 = merge %4 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %10 = merge %5 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %11 = merge %6 {handshake.bb = 1 : ui32, handshake.name = "merge2"} : <i32>
    %12 = merge %7 {handshake.bb = 1 : ui32, handshake.name = "merge3"} : <i32>
    %result, %index = control_merge [%8]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %addressResult_2, %dataResult_3 = store[%11] %9 {handshake.bb = 1 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_4, %dataResult_5 = store[%12] %10 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 1 : ui32, handshake.name = "end0"} %9, %0#2, %arg2 : <i32>, <>, <>
  }
}


// -----
module {
  handshake.func @mixLSQAndMCLoads(%arg0: memref<64xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %outputs:3, %memEnd = mem_controller[%arg0 : memref<64xi32>] %arg1 (%addressResult_0, %addressResult_4, %0#2, %0#3, %0#4) %result {connectedBlocks = [0 : i32, 1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %0:5 = lsq[MC] (%arg2, %addressResult, %result, %addressResult_2, %outputs#2)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %0#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = load[%2] %outputs#0 {handshake.bb = 0 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %4 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <i32>
    %5 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %6 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = merge %4 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %8 = merge %5 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %result, %index = control_merge [%6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %addressResult_2, %dataResult_3 = load[%7] %0#1 {handshake.bb = 1 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_4, %dataResult_5 = load[%8] %outputs#1 {handshake.bb = 1 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %9 = addi %dataResult_3, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    end {handshake.bb = 1 : ui32, handshake.name = "end0"} %9, %memEnd, %arg2 : <i32>, <>, <>
  }
}


// -----
module {
  handshake.func @mixLSQAndMCStores(%arg0: memref<64xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "in0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<64xi32>] %arg2 (%1, %addressResult_0, %dataResult_1, %8, %0#0, %0#1, %0#2) %result {connectedBlocks = [0 : i32, 1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0:3 = lsq[MC] (%arg3, %addressResult, %dataResult, %result, %addressResult_2, %dataResult_3, %outputs)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %2 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %4 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = store[%3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <i32>
    %6 = br %4 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %7 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = merge %5 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %10 = merge %6 {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %result, %index = control_merge [%7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %addressResult_2, %dataResult_3 = store[%10] %9 {handshake.bb = 1 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 1 : ui32, handshake.name = "end0"} %9, %memEnd, %arg3 : <i32>, <>, <>
  }
}


// -----
module {
  handshake.func @ifThenElseSameLSQGroup(%arg0: memref<64xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mem0", "in0", "mem0_start", "start"], resNames = ["out0", "mem0_end", "end"]} {
    %outputs:3, %memEnd = mem_controller[%arg0 : memref<64xi32>] %arg2 (%addressResult_2, %addressResult_6, %18, %0#1, %0#2, %0#3) %result_8 {connectedBlocks = [1 : i32, 2 : i32, 3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %0:4 = lsq[MC] (%arg3, %addressResult, %addressResult_10, %dataResult_11, %outputs#2)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%arg1] %0#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %3 = cmpi eq, %dataResult, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %4 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %7 = addi %4, %6 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %addressResult_2, %dataResult_3 = load[%7] %outputs#0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %8 = br %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "br0"} : <i32>
    %9 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br1"} : <i32>
    %10 = br %result {handshake.bb = 1 : ui32, handshake.name = "br2"} : <>
    %11 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %12 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %13 = constant %12 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %14 = addi %11, %13 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %addressResult_6, %dataResult_7 = load[%14] %outputs#1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %15 = br %dataResult_7 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <i32>
    %16 = br %11 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %17 = br %result_4 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %18 = constant %result_8 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %19 = mux %index_9 [%8, %15] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %20 = mux %index_9 [%9, %16] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result_8, %index_9 = control_merge [%10, %17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %addressResult_10, %dataResult_11 = store[%20] %19 {handshake.bb = 3 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %19, %memEnd, %arg3 : <i32>, <>, <>
  }
}

