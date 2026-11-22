module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 51, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.5" : memref<9xi8> = dense<[91, 51, 44, 45, 52, 44, 53, 93, 0]> {alignment = 1 : i64}
  func.func @wrap_if(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c3_i32 = arith.constant 3 : i32
    %c10_i32 = arith.constant 10 : i32
    %c11_i32 = arith.constant 11 : i32
    %c100_i32 = arith.constant 100 : i32
    %0 = memref.get_global @".str" : memref<4xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<4xi8>
    %3 = memref.get_global @".str.3" : memref<1xi8>
    %4 = memref.get_global @".str.4" : memref<4xi8>
    %5 = memref.get_global @".str.3" : memref<1xi8>
    %6 = memref.get_global @".str.5" : memref<9xi8>
    %7 = memref.get_global @".str.1" : memref<6xi8>
    %8 = memref.get_global @".str.2" : memref<4xi8>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%9: i32):  // 2 preds: ^bb0, ^bb3
    %10 = arith.extui %9 : i32 to i64
    %11 = arith.index_cast %10 : i64 to index
    %12 = memref.load %arg0[%11] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %13 = "dynamatic.prediction_marker"(%12) {dynamatic.predict = {location = "start", marker = 1 : i32, type = "int", values = "[3]"}} : (i32) -> i32
    %14 = arith.muli %13, %c3_i32 : i32
    %15 = "dynamatic.prediction_marker"(%14) {dynamatic.predict = {location = "end", marker = 1 : i32, type = "", values = ""}} : (i32) -> i32
    %16 = arith.cmpi sgt, %13, %c0_i32 : i32
    cf.cond_br %16, ^bb2, ^bb3(%15 : i32)
  ^bb2:  // pred: ^bb1
    %17 = "dynamatic.prediction_marker"(%15) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[3,-4,5]"}} : (i32) -> i32
    %18 = arith.addi %17, %arg2 : i32
    %19 = arith.muli %18, %c10_i32 : i32
    %20 = arith.extui %9 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %19, %arg1[%21] {handshake.name = "store1"} : memref<100xi32>
    cf.br ^bb3(%17 : i32)
  ^bb3(%22: i32):  // 2 preds: ^bb1, ^bb2
    %23 = arith.subi %22, %arg2 : i32
    %24 = arith.muli %23, %c11_i32 : i32
    %25 = arith.extui %9 : i32 to i64
    %26 = arith.index_cast %25 : i64 to index
    memref.store %24, %arg0[%26] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xi32>
    %27 = arith.addi %9, %c1_i32 : i32
    %28 = arith.cmpi ult, %27, %c100_i32 : i32
    cf.cond_br %28, ^bb1(%27 : i32), ^bb4
  ^bb4:  // pred: ^bb3
    return
  }
}
