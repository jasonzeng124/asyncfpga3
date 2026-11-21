module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 55, 93, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64, handshake.name = "global3"}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64, handshake.name = "global4"}
  func.func @divergent_paths(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: memref<100xi32> {handshake.arg_name = "b"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c100_i32 = arith.constant {handshake.name = "constant6"} 100 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c2_i32 = arith.constant {handshake.name = "constant8"} 2 : i32
    %c255_i32 = arith.constant {handshake.name = "constant9"} 255 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {dynamatic.predict = {location = "start", marker = 3 : i32, type = "int", values = "[7]"}, dynamatic.predict.result_idx = 0 : i32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : memref<100xi32>
    %4 = arith.xori %3, %c255_i32 {handshake.name = "xori0"} : i32
    %5 = arith.addi %4, %c2_i32 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "addi0"} : i32
    %6 = arith.shli %4, %c1_i32 {handshake.name = "shli0"} : i32
    %7 = arith.addi %4, %6 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.name = "addi2"} : i32
    %8 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast1"} : i64 to index
    memref.store %5, %arg0[%9] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : memref<100xi32>
    %10 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    memref.store %7, %arg1[%11] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : memref<100xi32>
    %12 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %13 = arith.cmpi ult, %12, %c100_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

