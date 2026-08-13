module {
  handshake.func @test0(%arg0: !handshake.channel<i32>, %arg1: memref<8xi32>, %arg2: memref<8xi8>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["var1", "var0", "var2", "var0_start", "var2_start", "start"], resNames = ["var0_end", "var2_end", "end"]} {
    %0 = lsq[%arg2 : memref<8xi8>] (%arg4, %arg5, %addressResult_0, %dataResult_1, %arg5)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i8>, !handshake.control<>) -> !handshake.control<>
    %1:2 = lsq[%arg1 : memref<8xi32>] (%arg3, %arg5, %addressResult, %addressResult_2, %dataResult_3, %arg5)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%2] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %3 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i8>
    %addressResult_0, %dataResult_1 = store[%2] %3 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i8>, <i32>, <i8>
    %addressResult_2, %dataResult_3 = store[%2] %arg0 {handshake.bb = 1 : ui32, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 1 : ui32, handshake.name = "end0"} %1#1, %0, %arg5 : <>, <>, <>
  }
}


// -----
module {
  handshake.func @shrsi_giid(%arg0: !handshake.channel<i8>, %arg1: memref<2xi16>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["var5", "var1", "var1_start", "start"], resNames = ["var1_end", "end"]} {
    %0:2 = lsq[%arg1 : memref<2xi16>] (%arg2, %arg3, %addressResult, %addressResult_0, %dataResult_1, %arg3)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i16>, !handshake.control<>) -> (!handshake.channel<i16>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %0#0 {handshake.bb = 0 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : false}]>, handshake.name = "load0"} : <i32>, <i16>, <i32>, <i16>
    %2 = extsi %dataResult {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i16> to <i32>
    %3 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i32>
    %4 = shrsi %2, %3 {handshake.bb = 0 : ui32, handshake.name = "shrsi0"} : <i32>
    %5 = trunci %4 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %addressResult_0, %dataResult_1 = store[%1] %5 {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i32>, <i16>, <i32>, <i16>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %0#1, %arg3 : <>, <>
  }
}

