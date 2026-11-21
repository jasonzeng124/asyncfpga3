module {
  memref.global "private" constant @__const.main.a : memref<2xi8> = dense<[1, 0]> {alignment = 1 : i64}
  func.func @test_bool_array(%arg0: memref<2xi8>) -> i1 {
    %c1_i64 = arith.constant 1 : i64
    %c1_i8 = arith.constant 1 : i8
    %c0_i8 = arith.constant 0 : i8
    %c0 = arith.constant 0 : index
    %0 = memref.load %arg0[%c0] {handshake.name = "load0"} : memref<2xi8>
    %c1_i64_0 = arith.constant 1 : i64
    %1 = arith.index_cast %c1_i64_0 : i64 to index
    %2 = memref.load %arg0[%1] {handshake.name = "load1"} : memref<2xi8>
    %3 = arith.ori %0, %2 : i8
    %4 = arith.andi %3, %c1_i8 : i8
    %5 = arith.cmpi ne, %4, %c0_i8 : i8
    return %5 : i1
  }
}
