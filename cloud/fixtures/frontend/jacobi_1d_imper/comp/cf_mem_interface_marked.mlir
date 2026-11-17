module {
  func.func @jacobi_1d_imper(%arg0: memref<100xi32> {handshake.arg_name = "A"}, %arg1: memref<100xi32> {handshake.arg_name = "B"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    cf.br ^bb2(%c1_i32 : i32) {handshake.name = "br1"}
  ^bb2(%1: i32):  // 2 preds: ^bb1, ^bb2
    %c99_i32 = arith.constant {handshake.name = "constant6"} 99 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant7"} -1 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant8"} 1 : i32
    %2 = arith.addi %1, %c-1_i32 {handshake.name = "addi0"} : i32
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i32 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load0"} : memref<100xi32>
    %5 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    %7 = memref.load %arg0[%6] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load1"} : memref<100xi32>
    %8 = arith.addi %4, %7 {handshake.name = "addi1"} : i32
    %9 = arith.addi %1, %c1_i32_0 {handshake.name = "addi2"} : i32
    %10 = arith.extui %9 {handshake.name = "extui1"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    %12 = memref.load %arg0[%11] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : memref<100xi32>
    %13 = arith.addi %8, %12 {handshake.name = "addi3"} : i32
    %14 = arith.shli %13, %c1_i32_0 {handshake.name = "shli0"} : i32
    %15 = arith.addi %13, %14 {handshake.name = "addi7"} : i32
    %16 = arith.extui %1 {handshake.name = "extui2"} : i32 to i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast3"} : i64 to index
    memref.store %15, %arg1[%17] {handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : memref<100xi32>
    %18 = arith.addi %1, %c1_i32_0 {handshake.name = "addi4"} : i32
    %19 = arith.cmpi ult, %18, %c99_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %19, ^bb2(%18 : i32), ^bb3(%c1_i32_0 : i32) {handshake.name = "cond_br0"}
  ^bb3(%20: i32):  // 2 preds: ^bb2, ^bb3
    %c99_i32_1 = arith.constant {handshake.name = "constant9"} 99 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant10"} 1 : i32
    %21 = arith.extui %20 {handshake.name = "extui3"} : i32 to i64
    %22 = arith.index_cast %21 {handshake.name = "index_cast4"} : i64 to index
    %23 = memref.load %arg1[%22] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load4"} : memref<100xi32>
    %24 = arith.extui %20 {handshake.name = "extui4"} : i32 to i64
    %25 = arith.index_cast %24 {handshake.name = "index_cast5"} : i64 to index
    memref.store %23, %arg0[%25] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : memref<100xi32>
    %26 = arith.addi %20, %c1_i32_2 {handshake.name = "addi5"} : i32
    %27 = arith.cmpi ult, %26, %c99_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %27, ^bb3(%26 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    %c3_i32 = arith.constant {handshake.name = "constant11"} 3 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant12"} 1 : i32
    %28 = arith.addi %0, %c1_i32_3 {handshake.name = "addi6"} : i32
    %29 = arith.cmpi ult, %28, %c3_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb5 {handshake.name = "cond_br2"}
  ^bb5:  // pred: ^bb4
    return {handshake.name = "return0"}
  }
}

