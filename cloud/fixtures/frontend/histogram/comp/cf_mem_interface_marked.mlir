module {
  func.func @histogram(%arg0: memref<1000xi32> {handshake.arg_name = "feature"}, %arg1: memref<1000xf32> {handshake.arg_name = "weight"}, %arg2: memref<1000xf32> {handshake.arg_name = "hist"}, %arg3: i32 {handshake.arg_name = "n"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg3, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    %7 = memref.load %arg1[%6] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<1000xf32>
    %8 = arith.index_cast %4 {handshake.name = "index_cast2"} : i32 to index
    %9 = memref.load %arg2[%8] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : memref<1000xf32>
    %10 = arith.addf %9, %7 {handshake.name = "addf0"} : f32
    %11 = arith.index_cast %4 {handshake.name = "index_cast3"} : i32 to index
    memref.store %10, %arg2[%11] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : memref<1000xf32>
    %12 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %13 = arith.cmpi slt, %12, %arg3 {handshake.name = "cmpi1"} : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}

