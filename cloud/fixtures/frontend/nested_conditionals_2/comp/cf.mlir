module {
  memref.global "private" constant @".str" : memref<4xi8> = dense<[91, 50, 93, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<6xi8> = dense<[115, 116, 97, 114, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<4xi8> = dense<[105, 110, 116, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.3" : memref<1xi8> = dense<0> {alignment = 1 : i64}
  memref.global "private" constant @".str.4" : memref<4xi8> = dense<[101, 110, 100, 0]> {alignment = 1 : i64}
  func.func @nested_conditionals_2(%arg0: memref<100xi32>, %arg1: i32) {
    %c10_i32 = arith.constant 10 : i32
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c5_i32 = arith.constant 5 : i32
    %c2_i32 = arith.constant 2 : i32
    %c3_i32 = arith.constant 3 : i32
    %c100_i32 = arith.constant 100 : i32
    %0 = memref.get_global @".str" : memref<4xi8>
    %1 = memref.get_global @".str.1" : memref<6xi8>
    %2 = memref.get_global @".str.2" : memref<4xi8>
    %3 = memref.get_global @".str.3" : memref<1xi8>
    %4 = memref.get_global @".str.4" : memref<4xi8>
    %5 = memref.get_global @".str.3" : memref<1xi8>
    %6 = arith.muli %arg1, %c10_i32 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%7: i32):  // 2 preds: ^bb0, ^bb4
    %8 = arith.extui %7 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg0[%9] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<100xi32>
    %11 = "dynamatic.prediction_marker"(%10) {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[2]"}} : (i32) -> i32
    %12 = arith.shli %11, %c1_i32 : i32
    %13 = arith.cmpi sgt, %11, %c1_i32 : i32
    cf.cond_br %13, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %14 = arith.cmpi sgt, %arg1, %c5_i32 : i32
    %15 = arith.shli %11, %c2_i32 : i32
    %16 = arith.addi %12, %arg1 : i32
    %17 = arith.select %14, %15, %16 : i32
    cf.br ^bb4(%17 : i32)
  ^bb3:  // pred: ^bb1
    %18 = arith.addi %6, %12 : i32
    cf.br ^bb4(%18 : i32)
  ^bb4(%19: i32):  // 2 preds: ^bb2, ^bb3
    %20 = arith.addi %19, %c3_i32 : i32
    %21 = "dynamatic.prediction_marker"(%20) {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}} : (i32) -> i32
    %22 = arith.extui %7 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    memref.store %21, %arg0[%23] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<100xi32>
    %24 = arith.addi %7, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %c100_i32 : i32
    cf.cond_br %25, ^bb1(%24 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    return
  }
}
