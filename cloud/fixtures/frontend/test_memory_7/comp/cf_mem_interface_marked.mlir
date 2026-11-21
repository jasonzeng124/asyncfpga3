module {
  func.func @test_memory_7(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) {
    %c2_i32 = arith.constant {handshake.name = "constant0"} 2 : i32
    %0 = arith.cmpi sgt, %arg1, %c2_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c2_i32 : i32), ^bb4 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32 = arith.constant {handshake.name = "constant6"} 0 : i32
    %c5_i32 = arith.constant {handshake.name = "constant7"} 5 : i32
    %c-2_i32 = arith.constant {handshake.name = "constant8"} -2 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant9"} -1 : i32
    %2 = arith.addi %1, %c-1_i32 {handshake.name = "addi0"} : i32
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i32 to index
    %4 = memref.load %arg0[%3] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : memref<4xi32>
    %5 = arith.addi %1, %c-2_i32 {handshake.name = "addi1"} : i32
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i32 to index
    %7 = memref.load %arg0[%6] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : memref<4xi32>
    %8 = arith.addi %4, %7 {handshake.name = "addi2"} : i32
    %9 = arith.addi %8, %c5_i32 {handshake.name = "addi3"} : i32
    %10 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    memref.store %9, %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : memref<4xi32>
    %12 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast3"} : i64 to index
    %14 = memref.load %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load3"} : memref<4xi32>
    %15 = arith.cmpi sgt, %14, %c0_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb2, ^bb3 {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c0_i32_0 = arith.constant {handshake.name = "constant10"} 0 : i32
    %16 = arith.extui %1 {handshake.name = "extui2"} : i32 to i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast4"} : i64 to index
    memref.store %c0_i32_0, %arg0[%17] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : memref<4xi32>
    cf.br ^bb3 {handshake.name = "br0"}
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant11"} 1 : i32
    %18 = arith.addi %1, %c1_i32 {handshake.name = "addi4"} : i32
    %19 = arith.cmpi slt, %18, %arg1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %19, ^bb1(%18 : i32), ^bb4 {handshake.name = "cond_br2"}
  ^bb4:  // 2 preds: ^bb0, ^bb3
    return {handshake.name = "return0"}
  }
}

