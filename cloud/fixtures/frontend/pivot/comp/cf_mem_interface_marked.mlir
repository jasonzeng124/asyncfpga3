module {
  func.func @pivot(%arg0: memref<1000xi32> {handshake.arg_name = "x"}, %arg1: memref<1000xi32> {handshake.arg_name = "a"}, %arg2: i32 {handshake.arg_name = "n"}, %arg3: i32 {handshake.arg_name = "k"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.addi %arg3, %c1_i32 {handshake.name = "addi0"} : i32
    %1 = arith.cmpi slt, %arg3, %arg2 {handshake.name = "cmpi0"} : i32
    cf.cond_br %1, ^bb1(%0, %c0_i32 : i32, i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32_0 = arith.constant {handshake.name = "constant2"} 1 : i32
    %4 = arith.index_cast %arg3 {handshake.name = "index_cast0"} : i32 to index
    memref.store %3, %arg0[%4] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : memref<1000xi32>
    %5 = arith.index_cast %arg3 {handshake.name = "index_cast1"} : i32 to index
    %6 = memref.load %arg0[%5] {handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.index_cast %2 {handshake.name = "index_cast2"} : i32 to index
    %8 = memref.load %arg1[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<1000xi32>
    %9 = arith.index_cast %2 {handshake.name = "index_cast3"} : i32 to index
    %10 = memref.load %arg0[%9] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<1000xi32>
    %11 = arith.muli %8, %10 {handshake.name = "muli0"} : i32
    %12 = arith.subi %6, %11 {handshake.name = "subi0"} : i32
    %13 = arith.addi %2, %c1_i32_0 {handshake.name = "addi1"} : i32
    %14 = arith.cmpi slt, %2, %arg2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}

