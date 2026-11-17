module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 51, 93, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64, handshake.name = "global3"}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64, handshake.name = "global4"}
  memref.global "private" constant @".str.5" : memref<9xi8> = dense<[91, 51, 44, 45, 52, 44, 53, 93, 0]> {alignment = 1 : i64, handshake.name = "global5"}
  func.func @wrap_if(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: memref<100xi32> {handshake.arg_name = "b"}, %arg2: i32 {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %4 = "dynamatic.prediction_marker"(%3) {dynamatic.predict = {location = "start", marker = 1 : i32, type = "int", values = "[3]"}, handshake.name = "prediction_marker0"} : (i32) -> i32
    %5 = arith.shli %4, %c1_i32 {handshake.name = "shli0"} : i32
    %6 = arith.addi %4, %5 {handshake.name = "addi2"} : i32
    %7 = "dynamatic.prediction_marker"(%6) {dynamatic.predict = {location = "end", marker = 1 : i32, type = "", values = ""}, handshake.name = "prediction_marker1"} : (i32) -> i32
    %8 = arith.cmpi sgt, %4, %c0_i32_0 {handshake.name = "cmpi0"} : i32
    cf.cond_br %8, ^bb2, ^bb3(%7 : i32) {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c1_i32_1 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c3_i32 = arith.constant {handshake.name = "constant10"} 3 : i32
    %9 = "dynamatic.prediction_marker"(%7) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[3,-4,5]"}, handshake.name = "prediction_marker2"} : (i32) -> i32
    %10 = arith.addi %9, %arg2 {handshake.name = "addi0"} : i32
    %11 = arith.shli %10, %c1_i32_1 {handshake.name = "shli1"} : i32
    %12 = arith.shli %10, %c3_i32 {handshake.name = "shli2"} : i32
    %13 = arith.addi %11, %12 {handshake.name = "addi3"} : i32
    %14 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast1"} : i64 to index
    memref.store %13, %arg1[%15] {handshake.name = "store1"} : memref<100xi32>
    cf.br ^bb3(%9 : i32) {handshake.name = "br1"}
  ^bb3(%16: i32):  // 2 preds: ^bb1, ^bb2
    %c100_i32 = arith.constant {handshake.name = "constant11"} 100 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c3_i32_3 = arith.constant {handshake.name = "constant13"} 3 : i32
    %17 = arith.subi %16, %arg2 {handshake.name = "subi0"} : i32
    %18 = arith.shli %17, %c1_i32_2 {handshake.name = "shli3"} : i32
    %19 = arith.shli %17, %c3_i32_3 {handshake.name = "shli4"} : i32
    %20 = arith.addi %18, %19 {handshake.name = "addi4"} : i32
    %21 = arith.addi %17, %20 {handshake.name = "addi5"} : i32
    %22 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %23 = arith.index_cast %22 {handshake.name = "index_cast2"} : i64 to index
    memref.store %21, %arg0[%23] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xi32>
    %24 = arith.addi %0, %c1_i32_2 {handshake.name = "addi1"} : i32
    %25 = arith.cmpi ult, %24, %c100_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %25, ^bb1(%24 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

