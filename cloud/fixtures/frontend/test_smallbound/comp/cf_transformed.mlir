module {
  func.func @test_smallbound(%arg0: memref<4xi32> {handshake.arg_name = "x"}, %arg1: memref<2xi32> {handshake.arg_name = "y"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant5"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb2
    %c2_i32 = arith.constant {handshake.name = "constant6"} 2 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c0 = arith.constant {handshake.name = "constant8"} 0 : index
    %c1_i64 = arith.constant {handshake.name = "constant9"} 1 : i64
    %4 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %5 = memref.load %arg1[%4] {handshake.name = "load0"} : memref<2xi32>
    %6 = memref.load %arg0[%c0] {handshake.name = "load1"} : memref<4xi32>
    %7 = arith.addi %5, %6 {handshake.name = "addi0"} : i32
    %8 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.shli %2, %c1_i64 {handshake.name = "shli0"} : i64
    %10 = arith.addi %9, %8 {handshake.name = "addi1"} : i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast1"} : i64 to index
    memref.store %7, %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    %12 = arith.addi %3, %c1_i32 {handshake.name = "addi2"} : i32
    %13 = arith.cmpi ult, %12, %c2_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %13, ^bb2(%12 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c2_i32_1 = arith.constant {handshake.name = "constant10"} 2 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant11"} 1 : i32
    %14 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %15 = arith.cmpi ult, %14, %c2_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

