module {
  func.func @test_stdint(%arg0: memref<100xi8> {handshake.arg_name = "a"}, %arg1: i8 {handshake.arg_name = "b"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c100_i32 = arith.constant {handshake.name = "constant3"} 100 : i32
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<100xi8>
    %4 = arith.muli %3, %3 {handshake.name = "muli0"} : i8
    %5 = arith.muli %4, %3 {handshake.name = "muli1"} : i8
    %6 = arith.addi %5, %arg1 {handshake.name = "addi0"} : i8
    %7 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast1"} : i64 to index
    memref.store %6, %arg0[%8] {handshake.name = "store1"} : memref<100xi8>
    %9 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %10 = arith.cmpi ne, %9, %c100_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %10, ^bb1(%9 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

