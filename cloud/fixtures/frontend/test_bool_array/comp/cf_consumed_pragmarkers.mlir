module {
  memref.global "private" constant @__const.main.a : memref<2xi8> = dense<[1, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @test_bool_array(%arg0: memref<2xi8> {handshake.arg_name = "a"}) -> i1 {
    %c1 = arith.constant {handshake.name = "constant0"} 1 : index
    %c1_i8 = arith.constant {handshake.name = "constant1"} 1 : i8
    %c0_i8 = arith.constant {handshake.name = "constant2"} 0 : i8
    %c0 = arith.constant {handshake.name = "constant3"} 0 : index
    %0 = memref.load %arg0[%c0] {handshake.name = "load0"} : memref<2xi8>
    %1 = memref.load %arg0[%c1] {handshake.name = "load1"} : memref<2xi8>
    %2 = arith.ori %0, %1 {handshake.name = "ori0"} : i8
    %3 = arith.andi %2, %c1_i8 {handshake.name = "andi0"} : i8
    %4 = arith.cmpi ne, %3, %c0_i8 {handshake.name = "cmpi0"} : i8
    return {handshake.name = "return0"} %4 : i1
  }
}

