Module Module2
    Public Const LASTM = 4
    Public a(2) As Double
    Private n As Integer
    Private Sx2 As Double
    Private Sx As Double
    Private Sxy As Double
    Private Sy As Double
    Private Sx3 As Double
    Private Sx2y As Double
    Private Sx4 As Double

    Public Function getTstmp() As String()
        Dim dt = DateTime.Now
        Dim s() = {
            dt.ToString("yyyy/MM/dd,HH:mm"),
            dt.ToString("yyyyMM") & "," & dt.ToString("%d") & "," & (Integer.Parse(dt.ToString("%H")) * 60 + Integer.Parse(dt.ToString("%m"))).ToString
        }
        Return s
    End Function

    Public Sub Int二次回帰()
        a(0) = 0 : a(1) = 0 : a(2) = 0
        n = 0 : Sx2 = 0 : Sx = 0 : Sxy = 0 : Sy = 0 : Sx3 = 0 : Sx2y = 0 : Sx4 = 0
    End Sub

    Public Sub addData(ByVal x As Double, ByVal y As Double)
        n += 1
        Dim x2 = x * x
        Sx2 += x2
        Sx += x
        Sxy += x * y
        Sy += y
        Sx3 += x2 * x
        Sx2y += x2 * y
        Sx4 += x2 * x2
    End Sub

    Public Function get二次回帰係数() As Double()
        Dim SSxx = Sx2 - Sx * Sx / n
        Dim SSxy = Sxy - Sx * Sy / n
        Dim SSxx2 = Sx3 - Sx * Sx2 / n
        Dim SSx2y = Sx2y - Sx2 * Sy / n
        Dim SSx2x2 = Sx4 - Sx2 * Sx2 / n
        Dim D = SSxx * SSx2x2 - SSxx2 * SSxx2

        a(0) = (SSx2y * SSxx - SSxy * SSxx2) / D
        a(1) = (SSxy * SSx2x2 - SSx2y * SSxx2) / D
        a(2) = Sy / n - a(1) * Sx / n - a(0) * Sx2 / n

        Return a
    End Function

    Function Gauss_Jordan2(ByVal s As Single(,)) As Single()
        Dim i As Integer, j As Integer
        Dim p1(LASTM, LASTM) As Single
        Dim p2(LASTM - 1) As Single

        For i = 1 To LASTM
            For j = 1 To LASTM
                p1(i, j) = s(i - 1, 0) ^ (LASTM - j)
            Next
            p2(i - 1) = s(i, 1)
        Next
        Gauss_Jordan2 = Gauss_Jordan(p1, p2)

    End Function

    Function Gauss_Jordan(ByVal A As Single(,), ByVal p As Single()) As Single()
        Dim i As Long, j As Long, k As Long, Atemp, res
        Dim cols As Long, rows As Long, MaxVal As Double
        Dim Max_Ind As Double, temp As Double, hold

        '******************************************************
        '**  Function performs Gauss-Jordan decomposition on **
        '**  a pxp input matrix and returns the augmented    **
        '**  px2p matrix with the pxp identity matrix on the **
        '**  left hand side and the pxp matrix inverse on    **
        '**  the right hand side.                            **
        '******************************************************

        'Determine if function is used on worksheet
        cols = Int(A.Length / 2)
        rows = cols

        'Increase columns to add identity matrix
        cols = cols + cols
        ReDim hold(rows, rows)
        ReDim Atemp(rows, cols)
        ReDim res(rows - 1)

        'Augment matrix with identity matrix
        For i = 1 To rows
            For j = 1 To rows
                Atemp(i, j) = A(i, j)
                Atemp(i, j + rows) = 0.0#
            Next j
            Atemp(i, i + rows) = 1.0#
        Next i

        For i = 1 To rows

            MaxVal = Atemp(i, i)
            Max_Ind = i
            ' Sort procedure finds the greatest leading value
            For j = i + 1 To rows
                If Math.Abs(Atemp(j, i)) > Math.Abs(MaxVal) Then
                    MaxVal = Atemp(j, i)
                    Max_Ind = j
                End If
            Next j

            If MaxVal = 0 Then
                MsgBox(Prompt:="Matrix is singular!", Title:="Error")
                Return res
                Exit Function
            End If

            'Set pivot equal to 1 and swap rows if necessary
            For j = i To cols
                'row i into temporary storage if swap is needed
                temp = Atemp(i, j)
                'data from row max_ind into row i and divide by maxval
                Atemp(i, j) = Atemp(Max_Ind, j) / MaxVal
                'Swap the max_ind row with row i (if necessary)
                If Max_Ind <> i Then Atemp(Max_Ind, j) = temp
            Next j

            'Perform row operations to produce reduced row-echelon form
            For k = 1 To rows
                If k <> i Then              'Not the pivot
                    'store multiple of row
                    For j = 1 To cols
                        hold(k, j) = -Atemp(k, i) * Atemp(i, j)
                    Next j
                    'add together and replace the row
                    For j = 1 To cols
                        Atemp(k, j) = Atemp(k, j) + hold(k, j)
                    Next j
                End If
            Next k
        Next i

        For i = 1 To rows
            For j = 1 To rows
                res(i - 1) = res(i - 1) + Atemp(i, j) * p(i - 1)
            Next
            Console.WriteLine(res(i - 1))
        Next

        Gauss_Jordan = res
    End Function

End Module
