; NOTE: Assertions have been autogenerated by update_test_checks.py
; RUN: opt < %s -simplifycfg -verify-dom-info -S | FileCheck %s

; Test normal folding
define i32 @test1() {
; CHECK-LABEL: @test1(
; CHECK-NEXT:  TheDest:
; CHECK-NEXT:    ret i32 1234
;
  switch i32 5, label %Default [
  i32 0, label %Foo
  i32 1, label %Bar
  i32 2, label %Baz
  i32 5, label %TheDest
  ]
Default:
  ret i32 -1
Foo:
  ret i32 -2
Bar:
  ret i32 -3
Baz:
  ret i32 -4
TheDest:
  ret i32 1234
}

; Test folding to default dest
define i32 @test2() {
; CHECK-LABEL: @test2(
; CHECK-NEXT:  Default:
; CHECK-NEXT:    ret i32 1234
;
  switch i32 3, label %Default [
  i32 0, label %Foo
  i32 1, label %Bar
  i32 2, label %Baz
  i32 5, label %TheDest
  ]
Default:
  ret i32 1234
Foo:
  ret i32 -2
Bar:
  ret i32 -5
Baz:
  ret i32 -6
TheDest:
  ret i32 -8
}

; Test folding all to same dest
define i32 @test3(i1 %C) {
; CHECK-LABEL: @test3(
; CHECK-NEXT:  TheDest:
; CHECK-NEXT:    ret i32 1234
;
  br i1 %C, label %Start, label %TheDest
Start:          ; preds = %0
  switch i32 3, label %TheDest [
  i32 0, label %TheDest
  i32 1, label %TheDest
  i32 2, label %TheDest
  i32 5, label %TheDest
  ]
TheDest:
  ret i32 1234
}

; Test folding switch -> branch
define i32 @test4(i32 %C) {
; CHECK-LABEL: @test4(
; CHECK-NEXT:  L1:
; CHECK-NEXT:    [[COND:%.*]] = icmp eq i32 %C, 0
; CHECK-NEXT:    [[DOT:%.*]] = select i1 [[COND]], i32 1, i32 0
; CHECK-NEXT:    ret i32 [[DOT]]
;
  switch i32 %C, label %L1 [
  i32 0, label %L2
  ]
L1:
  ret i32 0
L2:
  ret i32 1
}

; Can fold into a cond branch!
define i32 @test5(i32 %C) {
; CHECK-LABEL: @test5(
; CHECK-NEXT:  L1:
; CHECK-NEXT:    [[COND:%.*]] = icmp eq i32 %C, 0
; CHECK-NEXT:    [[DOT:%.*]] = select i1 [[COND]], i32 1, i32 0
; CHECK-NEXT:    ret i32 [[DOT]]
;
  switch i32 %C, label %L1 [
  i32 0, label %L2
  i32 123, label %L1
  ]
L1:
  ret i32 0
L2:
  ret i32 1
}

