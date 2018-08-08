Imports System.Diagnostics
Imports System.IO
Imports System.IO.Compression
Imports System.Console
Imports System.Text
Imports System.Drawing
Imports System.Drawing.Drawing2D
Imports System.Windows.Forms
Imports System.Net
Imports System.Net.Mail

Module Module1
    Const 高血糖水準 = 200
    Const 低血糖水準 = 60
    Const 高血糖通知水準 = 140
    Const 低血糖通知水準 = 80
    Const 最小微係数分散 = 0.2
    Const センサ異常判定間隔 = 30
    Const DBOX_GLIMPD = "C:\Users\hiro\Dropbox\アプリ\Glimp\"
    Const DBOX_GLIMPD_GZ_UTF16 = DBOX_GLIMPD & "GlicemiaMisurazioni.csv.gz"
    Const DBOX_GLIMPD_CONV = DBOX_GLIMPD & "GlicemiaMisurazioni.csv"
    Const DBOX_GLIMPD_EVENT = DBOX_GLIMPD & "GlicemiaMisurazioniEvent.csv.gz"
    Const 直近データ列ファイル = DBOX_GLIMPD & "当日\data0.txt"
    Const 当日血糖値列ファイル = DBOX_GLIMPD & "当日\gdata.txt"
    Const 前日血糖値列ファイル = DBOX_GLIMPD & "前日\gdata.txt"
    Const 当日血糖値グラフ = DBOX_GLIMPD & "当日\gdata.txt"
    Const 前日血糖値グラフ = DBOX_GLIMPD & "前日\gdata.txt"
    Const 警告検証ファイル = DBOX_GLIMPD & "前日\check.txt"

    Const DOC_DIR = "C:\Users\hiro\Documents\glimp\"
    Const DOC_OUT_FULL = DOC_DIR & "GlicemiaMisurazioni.csv"
    Const GRAPH_DIR = "C:\Users\hiro\Pictures\"
    Const wDir = "C:\var\"
    Const utf16Csv = wDir & "GlicemiaMisurazioni.csv"
    Const convCsv = wDir & "tmp.csv"
    'Const OENC = "shift-jis"
    Const OENC = "utf-8"
    Const TH_Subline = 0.09
    Const Log_File = DOC_DIR & "glimp.log.txt"
    Const QuitFile = "watching.gz"
    Const ODF = -2000
    Const 最大イベント数 = 500
    Const MSG高血糖 = "高血糖予測通知"
    Const MSG低血糖 = "低血糖予測通知"
    Const SMBG催促MSG = "血糖値校正のためSMBGして下さい"
    Const CMD_LINEメッセージ送信 = "C:\Users\hiro\Desktop\PasteAndSendLineSMS.hmc -.lnk"
    Const FTPID = "diabetes2863"
    Const FTPPW = "XMk_n7mgW7~tSV2@f2kj"
    Const FTPSVR = "ftp://diabetes2863.web.fc2.com/"
    Const WEBGRAH = "3X10Y.png"

    Const D60x24 = 60 * 24 '一日（分）
    Const 持続型インスリン = "Night"
    Const 速攻型インスリン = "ヒューマログ"
    Const 持続型インスリン活性持続時間 = 60 * 24  '分
    Const 速攻型インスリン活性持続時間 = 60 * 3   '分
    Const 持続型インスリンオフセット時間 = 60 * 1   '分
    Const 速攻型インスリンオフセット時間 = 60 * 0.5 '分
    Const 持続型インスリンUnit数 = 2
    Const 速攻型インスリンUnit数 = 5
    Const 最大Glimp値 = 300
    Const SubFLen = 3
    Const SMBG_PCR As Integer = 5
    Const IL_Mg = 200
    Const 有効値 = 0.2
    Const 有効範囲 = 30 '分

    Const 解析範囲 = 40
    Const 解析単位 = 5
    Const 解析単位x2 = 10

    Private SMBG通知間隔 As Int64 = 8 '時間
    Private SMBG催促間隔 As Int64 = 1 '時間
    Private SMBG前回催促 As Int64 = -1

    Private センサID As String = ""
    Private dbgf As Boolean
    Private sw As StreamWriter
    Private psi As ProcessStartInfo                            'ProcessStartInfoオブジェクト
    Private proc As Process
    Private t_bk1 As Single                                    '
    Private g_bk1 As Single
    Private r_bk1 As Single
    Private str当日日付 As String
    Private str前日日付 As String

    Private センサ値列当日_Json As String = ""                'row data 当日 json format
    Private センサ値列前日_Json As String = ""                'row data 前日 json format
    Private センサ値列前々日_Json As String = ""              'row data 前々日 json format
    Private Glimp0値列当日_Json As String = ""                'glimp data 当日 json format
    Private Glimp0値列前日_Json As String = ""                'glimp data 前日 json format
    Private Glimp0値列前々日_Json As String = ""              'glimp data 前々日 json format

    Private 生Glimp0値列当日(D60x24 + 2, 1) As Single         'series glimp data 当日
    Private 生Glimp0値列前日(D60x24 + 2, 1) As Single         'series glimp data 前日
    Private 補間Glimp0値列当日(D60x24 + 2, 1) As Single       'series glimp data 当日
    Private 補間Glimp0値列前日(D60x24 + 2, 1) As Single       'series glimp data 前日

    Private 生センサ値列当日(D60x24 + 2, 1) As Single         'series row data 当日
    Private 生センサ値列前日(D60x24 + 2, 1) As Single         'series row data 前日
    Private 補間センサ値列当日(D60x24 + 2, 1) As Single       'series row data 当日
    Private 補間センサ値列前日(D60x24 + 2, 1) As Single       'series row data 前日

    Private 最終計測時刻 As Integer

    Private Last3dGlimp0値列(3 - 1, 1) As Single              '最新10分毎のGlimpデータ
    Private Last3dセンサ値列(3 - 1, 1) As Single              '最新10分毎のGlimpデータ
    Private Last5dGlimp0値列(5 - 1, 1) As Single              '最新5分毎のGlimpデータ
    Private Last5dセンサ値列(5 - 1, 1) As Single              '最新5分毎のGlimpデータ

    Private dセンサ値列4(4) As Single                         'series row data 当日’
    Private dGlimp0値列4(4) As Single                         'series glimp data 当日
    Private dセンサ値列8(7) As Single                         'series row data 当日’
    Private dGlimp0値列8(7) As Single                         'series glimp data 当日

    Private 直近Glimp0値列(4, 1) As Single
    Private 直近センサ値列(4, 1) As String
    Private 予測Glimp値列(4, 1) As Single
    Private 予測センサ値列(4, 1) As Single
    Private a10data(1, 144, 6) As Single
    Private a05data(1, 288, 8) As Single
    Private Event当日(最大イベント数, 1) As String
    Private Event前日(最大イベント数, 1) As String

    Private 補間インスリンレベル値列当日(D60x24, 1) As Single 'インスリン
    Private 補間インスリンレベル値列前日(D60x24, 1) As Single 'インスリン

    Private smbg当日(D60x24, 1) As Single                     'SMBG当日
    Private smbg前日(D60x24, 1) As Single                     'SMBG前日
    Private LastSmbg As Int64 = -1

    Private smbg_idx0 As Integer
    Private smbg_idx1 As Integer
    Private graphFn当日 As String
    Private graphFn前日 As String
    Private mgStep As Integer = 20
    Private th As System.Threading.Thread
    Private str最終計測時刻 As String
    Private str最終計測血糖値 As String
    Private b_graphs As String(,) = {
        {"C:\Users\hiro\Dropbox\アプリ\Glimp\当日\3X10Y.png", "3X10Y.png"},
        {"C:\Users\hiro\Dropbox\アプリ\Glimp\当日\3X10Y.png", "3X10Y.png"},
        {"C:\Users\hiro\Dropbox\アプリ\Glimp\前日\3X10Y.png", "3X10Y.png"}
    }
    Private watcher As New FileSystemWatcher

    Private Sub 配列初期化()
        センサ値列当日_Json = ""                 'row data 当日 json format
        センサ値列前日_Json = ""                 'row data 前日 json format
        センサ値列前々日_Json = ""               'row data 前々日 json format
        Glimp0値列当日_Json = ""                  'glimp data 当日 json format
        Glimp0値列前日_Json = ""                  'glimp data 前日 json format
        Glimp0値列前々日_Json = ""                'glimp data 前々日 json format

        ReDim 生センサ値列当日(D60x24 + 2, 1)   'series row data 当日
        ReDim 生センサ値列前日(D60x24 + 2, 1)   'series row data 前日
        ReDim 生Glimp0値列当日(D60x24 + 2, 1)    'series glimp data 当日
        ReDim 生Glimp0値列前日(D60x24 + 2, 1)    'series glimp data 前日

        Dim i As Integer
        For i = 0 To D60x24 + 2
            生センサ値列当日(i, 0) = (i - 1) * 1.0 : 生センサ値列当日(i, 1) = -1.0
            生センサ値列前日(i, 0) = (i - 1) * 1.0 : 生センサ値列前日(i, 1) = -1.0
            生Glimp0値列当日(i, 0) = (i - 1) * 1.0 : 生Glimp0値列当日(i, 1) = -1.0
            生Glimp0値列前日(i, 0) = (i - 1) * 1.0 : 生Glimp0値列前日(i, 1) = -1.0
        Next
        For i = 0 To D60x24
            補間インスリンレベル値列当日(i, 0) = i * 1.0 : 補間インスリンレベル値列当日(i, 1) = 0.0
            補間インスリンレベル値列前日(i, 0) = i * 1.0 : 補間インスリンレベル値列前日(i, 1) = 0.0
            smbg当日(i, 0) = i * 1.0 : smbg当日(i, 1) = -1.0
            smbg前日(i, 0) = i * 1.0 : smbg前日(i, 1) = -1.0
        Next

        graphFn当日 = wDir
        graphFn前日 = wDir
        LastSmbg = -1
        smbg_idx0 = 0
        smbg_idx1 = 0
    End Sub

    Private Function ssv2csv(ByVal s1 As String) As String
        '入力データフォーマット
        '00:不明
        '01:日月年時刻(DD/MM/YYY HH.mm.[00,30]
        '02:不明
        '03:体重
        '04:{06}=3,5の場合、センサ値。それ以外の場合、SMBG値又はブランク
        '05:{06}=3,5の場合、Glimp値。それ以外の場合、SMBG値又はブランク
        '06:[0,3,5]
        '07:{06}=3,5の場合、センサＩＤ。それ以外の場合、SMBG採血位置又はブランク
        '08:insulin dose unit
        '09:insulin name ログ・ランタス
        '10:不明
        '11:insulin inject position
        '12:Note
        Dim j As Integer
        Dim s2 As String
        s2 = s1.Substring(0, 1) & ","                                                  '不明
        s2 = s2 & s1.Substring(8, 4) & s1.Substring(4, 4) & s1.Substring(2, 2) & ","   '年月日
        s2 = s2 & s1.Substring(13, 2) & ":" & s1.Substring(16).Replace(";", ",") & "," '時分秒＋データ
        s2 = s2 & s1.Substring(8, 4) & s1.Substring(5, 2) & ","                        '年月
        If s1.Substring(2, 1) = "0" Then
            s2 = s2 & s1.Substring(3, 1) & ","                                         '日
        Else
            s2 = s2 & s1.Substring(2, 2) & ","                                         '日
        End If
        '通算分（全日）算出
        j = 0
        If s1.Substring(13, 1) = "0" Then
            j = j + 60 * Val(s1.Substring(14, 1))
        Else
            j = j + 60 * Val(s1.Substring(13, 2))
        End If
        If s1.Substring(16, 1) = "0" Then
            j = j + Val(s1.Substring(17, 1))
        Else
            j = j + Val(s1.Substring(16, 2))
        End If
        'If s1.Substring(19, 1) = "0" Then
        '    j = j + Val(s1.Substring(20, 1))
        'Else
        '    j = j + Val(s1.Substring(19, 2))
        'End If
        s2 = s2 & j.ToString                                                           '通算分（全日）
        ssv2csv = s2
    End Function

    Private Sub SetStr2Clipboard(ByVal o As Object)
        Dim msg As String = CType(o, String)
        Clipboard.SetText(msg)
    End Sub

    Private Sub ダミー主処理呼び出し() '処理本体呼び出し制御→
        Dim d1 As Date, d2 As Date
        System.Threading.Thread.Sleep(5000)
        d1 = File.GetLastWriteTime(DBOX_GLIMPD_GZ_UTF16)
        d2 = File.GetLastWriteTime(DBOX_GLIMPD_CONV)
        If d1 > d2 Then
            ログ出力("Update Start " & d1.ToString & "," & d2.ToString)
            'psi.FileName = """C:\Program Files\7-Zip\7z.exe""" '起動するファイルのパスを指定する
            'psi.Arguments = """e"" """ & DBOX_GLIMPD_GZ_UTF16 & """ ""-aoa"" ""-o" & wDir & """" 'コマンドライン引数を指定する

            'proc = Process.Start(psi) ' 外部コマンドを起動する

            'proc.WaitForExit() ' 外部コマンドが終了するまで無期限で待つ
            'proc.WaitForExit(10000) ' 待機する時間を指定（10秒だけ）して待つ

            'If (proc.HasExited = False) Then ' 外部コマンドが終了しているか確認する
            'If (proc.CloseMainWindow() = False) Then ' 外部コマンドがまだ起動中の場合は、メインウィンドウのクローズイベントを発生させる
            ' メインウィンドウがモーダルボックスを表示させているなどして終了できない場合は false がリターンされる
            'End If
            'Debug.Print("test")
            'End If

            'th = New System.Threading.Thread(AddressOf SetStr2Clipboard)
            'th.SetApartmentState(System.Threading.ApartmentState.STA)
            'th.Start("更新開始")
            'th.Join()

            'proc = System.Diagnostics.Process.Start("C:\Users\hiro\Desktop\PasteAndSendLineSMS.hmc -.lnk")
            'proc.WaitForExit(20000) ' 待機する時間を指定（10秒だけ）して待つ
            'If (proc.HasExited = False) Then ' 外部コマンドが終了しているか確認する
            'Debug.Print("NG")
            'End If


            本処理()
        Else
            Debug.Print("skip")
        End If
    End Sub

    Private Sub ファイル解凍()
        Dim num As Integer
        Dim buf(1024) As Byte                                                                ' 1Kbytesずつ処理する

        Dim inStream As New FileStream(DBOX_GLIMPD_GZ_UTF16, FileMode.Open, FileAccess.Read) ' 入力ストリーム
        Dim decompStream As New GZipStream(inStream, CompressionMode.Decompress)             ' 解凍ストリーム
        Dim outStream As New FileStream(utf16Csv, FileMode.Create)                           ' 出力ストリーム

        Using inStream
            Using outStream
                Using decompStream
                    Do
                        num = decompStream.Read(buf, 0, buf.Length)
                        If num <= 0 Then Exit Do
                        outStream.Write(buf, 0, num)
                    Loop
                End Using
            End Using
        End Using

    End Sub

    Private Sub 当日LineConv(ByRef e() As String)
        Dim ds As Single 'インスリンレベル
        If e(7) = "3" Or e(7) = "5" Then
            Debug.Print("add dline0")
            If Glimp0値列当日_Json = "" Then
                センサID = e(8)
                最終計測時刻 = e(16)
                str最終計測血糖値 = e(6)
                str最終計測時刻 = Left(e(2), 5)
                str当日日付 = e(0) & "," & e(1)
                Glimp0値列当日_Json = "[[" & e(16) & "," & e(6) & "]"
                graphFn当日 = graphFn当日 & e(1).Replace("/", "-")
            Else
                Glimp0値列当日_Json = Glimp0値列当日_Json & ",[" & e(16) & "," & e(6) & "]"
            End If
            If センサ値列当日_Json = "" Then
                センサ値列当日_Json = "[[" & e(16) & "," & e(5) & "]"
            Else
                センサ値列当日_Json = センサ値列当日_Json & ",[" & e(16) & "," & e(5) & "]"
            End If
            If センサID = e(8) Then
                生Glimp0値列当日(e(16) + 1, 1) = e(6)
                生センサ値列当日(e(16) + 1, 1) = e(5)
            Else
                生Glimp0値列当日(e(16), 1) = e(6)
                生センサ値列当日(e(16), 1) = e(5)
                生Glimp0値列当日(e(16) + 1, 1) = -2
                生センサ値列当日(e(16) + 1, 1) = -2
                センサID = e(8)
            End If
            t_bk1 = D60x24 + e(16)
            g_bk1 = e(6)
            r_bk1 = e(5)
        ElseIf e(7) = "0" And e(10) = 持続型インスリン Then
            ds = e(9) * 持続型インスリンUnit数 / 持続型インスリン活性持続時間
            e(16) = e(16) + 持続型インスリンオフセット時間
            If e(16) > D60x24 Then
                ログ出力("ほっとく当日持続")
            ElseIf e(16) = D60x24 Then
                ログ出力("ほっとく当日持続")
            Else
                For ii = 1 To 持続型インスリン活性持続時間 + 1
                    If e(16) + ii > D60x24 Then Exit For
                    補間インスリンレベル値列当日(e(16) + ii, 1) _
                        = 補間インスリンレベル値列当日(e(16) + ii, 1) + ds
                Next
            End If
            If e(6) <> "" AndAlso e(6) = e(5) Then 'インスリン注射、SMBG同時記入対応
                smbg当日(e(16), 1) = e(6) : smbg_idx0 += 1
                If LastSmbg < 0 Then
                    LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
                End If
            End If
            e(16) = e(16) - 持続型インスリンオフセット時間
            ds = 0
        ElseIf e(7) = "0" And e(10) = 速攻型インスリン Then
            ds = e(9) * 速攻型インスリンUnit数 / 速攻型インスリン活性持続時間
            e(16) = e(16) + 速攻型インスリンオフセット時間
            If e(16) > D60x24 Then
                ログ出力("ほっとく当日速攻")
            ElseIf e(16) = D60x24 Then
                ログ出力("ほっとく当日速攻")
            Else
                For ii = 0 To 速攻型インスリン活性持続時間
                    If e(16) + ii > D60x24 Then Exit For
                    補間インスリンレベル値列当日(e(16) + ii, 1) _
                        = 補間インスリンレベル値列当日(e(16) + ii, 1) + ds
                Next
            End If
            If e(6) <> "" AndAlso e(6) = e(5) Then 'インスリン注射、SMBG同時記入対応
                smbg当日(e(16), 1) = e(6) : smbg_idx0 += 1
                If LastSmbg < 0 Then
                    LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
                End If
            End If
            e(16) = e(16) - 速攻型インスリンオフセット時間
            ds = 0
        ElseIf e(7) = "0" And e(8) <> "" Then
            smbg当日(e(16), 1) = e(6) : smbg_idx0 += 1
            If LastSmbg < 0 Then
                LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
            End If
        End If
    End Sub

    Private Sub 前日LineConv(ByRef e() As String)
        Dim ds As Single                                            'インスリンレベル
        If e(7) = "3" Or e(7) = "5" Then
            If Glimp0値列前日_Json = "" Then
                str前日日付 = e(0) & "," & e(1)
                生Glimp0値列当日(0, 0) = -1.0 * (D60x24 - e(16))
                生Glimp0値列当日(0, 1) = e(6)
                Glimp0値列当日_Json = Glimp0値列当日_Json & "]"
                Glimp0値列前日_Json = "[[" & e(16) & "," & e(6) & "]"
                graphFn前日 = graphFn前日 & e(1).Replace("/", "-")
                生Glimp0値列前日(D60x24 + 2, 0) = t_bk1
                生Glimp0値列前日(D60x24 + 2, 1) = g_bk1
            Else
                Glimp0値列前日_Json = Glimp0値列前日_Json & ",[" & e(16) & "," & e(6) & "]"
            End If
            If センサ値列前日_Json = "" Then
                生センサ値列当日(0, 0) = -1.0 * (D60x24 - e(16))
                生センサ値列当日(0, 1) = e(5)
                センサ値列当日_Json = センサ値列当日_Json & "]"
                センサ値列前日_Json = "[[" & e(16) & "," & e(5) & "]"
                生センサ値列前日(D60x24 + 2, 0) = t_bk1
                生センサ値列前日(D60x24 + 2, 1) = r_bk1
            Else
                センサ値列前日_Json = センサ値列前日_Json & ",[" & e(16) & "," & e(5) & "]"
            End If
            If センサID = e(8) Then
                生Glimp0値列前日(e(16) + 1, 1) = e(6)
                生センサ値列前日(e(16) + 1, 1) = e(5)
            Else
                生Glimp0値列前日(e(16), 1) = e(6)
                生センサ値列前日(e(16), 1) = e(5)
                生Glimp0値列前日(e(16) + 1, 1) = -2
                生センサ値列前日(e(16) + 1, 1) = -2
                センサID = e(8)
            End If
            t_bk1 = D60x24 + e(16)
            g_bk1 = e(6)
            r_bk1 = e(5)
        ElseIf e(7) = "0" And e(10) = 持続型インスリン Then
            ds = e(9) * 持続型インスリンUnit数 / 持続型インスリン活性持続時間
            e(16) = e(16) + 持続型インスリンオフセット時間
            If e(16) >= D60x24 Then
                For ii = 0 To 持続型インスリン活性持続時間
                    If e(16) - D60x24 + ii > D60x24 Then Exit For
                    補間インスリンレベル値列当日(e(16) - D60x24 + ii, 1) _
                        = 補間インスリンレベル値列当日(e(16) - D60x24 + ii, 1) + ds
                Next
            Else
                For ii = 0 To 持続型インスリン活性持続時間
                    If e(16) + ii > D60x24 Then
                        補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) _
                            = 補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) + ds
                    ElseIf e(16) + ii = D60x24 Then
                        補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) _
                            = 補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) + ds
                        補間インスリンレベル値列前日(e(16) + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) + ii, 1) + ds
                    Else
                        補間インスリンレベル値列前日(e(16) + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) + ii, 1) + ds
                    End If
                Next
            End If
            If e(6) <> "" AndAlso e(6) = e(5) Then 'インスリン注射、SMBG同時記入対応
                smbg前日(e(16), 1) = e(6) : smbg_idx1 += 1
                If LastSmbg < 0 Then
                    LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
                End If
            End If
            e(16) = e(16) - 持続型インスリンオフセット時間
            ds = 0
        ElseIf e(7) = "0" And e(10) = 速攻型インスリン Then
            ds = e(9) * 速攻型インスリンUnit数 / 速攻型インスリン活性持続時間
            e(16) = e(16) + 速攻型インスリンオフセット時間
            If e(16) >= D60x24 Then
                For ii = 0 To 速攻型インスリン活性持続時間
                    If e(16) - D60x24 + ii > D60x24 Then Exit For
                    補間インスリンレベル値列当日(e(16) - D60x24 + ii, 1) _
                        = 補間インスリンレベル値列当日(e(16) - D60x24 + ii, 1) + ds
                Next
            Else
                For ii = 0 To 速攻型インスリン活性持続時間
                    If e(16) + ii > D60x24 Then
                        補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) _
                            = 補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) + ds
                    ElseIf e(16) + ii = D60x24 Then
                        補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) _
                            = 補間インスリンレベル値列当日(e(16) + ii - D60x24, 1) + ds
                        補間インスリンレベル値列前日(e(16) + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) + ii, 1) + ds
                    Else
                        補間インスリンレベル値列前日(e(16) + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) + ii, 1) + ds
                    End If
                Next
            End If
            If e(6) <> "" AndAlso e(6) = e(5) Then 'インスリン注射、SMBG同時記入対応
                smbg前日(e(16), 1) = e(6) : smbg_idx1 += 1
                If LastSmbg < 0 Then
                    LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
                End If
            End If
            e(16) = e(16) - 速攻型インスリンオフセット時間
            ds = 0
        ElseIf e(7) = "0" And e(8) <> "" Then
            smbg前日(e(16), 1) = e(6) : smbg_idx1 += 1
            If LastSmbg < 0 Then
                LastSmbg = DateTime.Parse(e(1) & " " & e(2).Substring(0, 5) & ":00").Ticks
            End If
        End If
    End Sub

    Private Sub 前々日LineConv(ByRef e() As String)
        Dim ds As Single                                            'インスリンレベル
        If e(7) = "3" Or e(7) = "5" Then
            If Glimp0値列前々日_Json = "" Then
                生Glimp0値列前日(0, 0) = -1.0 * (D60x24 - e(16))
                生Glimp0値列前日(0, 1) = e(6)
                Glimp0値列前日_Json = Glimp0値列前日_Json & "]"
                Glimp0値列前々日_Json = "[["
            End If
            If センサ値列前々日_Json = "" Then
                生センサ値列前日(0, 0) = -1.0 * (D60x24 - e(16))
                生センサ値列前日(0, 1) = e(5)
                センサ値列前日_Json = センサ値列前日_Json & "]"
                センサ値列前々日_Json = "[["
            End If
        ElseIf e(7) = "0" And e(10) = 持続型インスリン Then
            ds = e(9) * 持続型インスリンUnit数 / 持続型インスリン活性持続時間
            e(16) = e(16) + 持続型インスリンオフセット時間
            If e(16) >= D60x24 Then
                'Console.WriteLine("ほっとく前々日持続")
                For ii = 0 To 持続型インスリン活性持続時間
                    If e(16) - D60x24 + ii < D60x24 Then
                        補間インスリンレベル値列前日(e(16) - D60x24 + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) - D60x24 + ii, 1) + ds
                    ElseIf e(16) - D60x24 + ii = D60x24 Then
                        補間インスリンレベル値列前日(e(16) - D60x24 + ii, 1) _
                            = 補間インスリンレベル値列前日(e(16) - D60x24 + ii, 1) + ds
                        補間インスリンレベル値列当日(e(16) - D60x24 - D60x24 + ii, 1) _
                            = 補間インスリンレベル値列当日(e(16) - D60x24 - D60x24 + ii, 1) + ds
                    Else
                        補間インスリンレベル値列当日(e(16) - D60x24 - D60x24 + ii, 1) _
                            = 補間インスリンレベル値列当日(e(16) - D60x24 - D60x24 + ii, 1) + ds
                    End If
                Next
            Else
                For ii = 0 To 持続型インスリン活性持続時間
                    If e(16) + ii >= D60x24 Then
                        補間インスリンレベル値列前日(e(16) + ii - D60x24, 1) = _
                            補間インスリンレベル値列前日(e(16) + ii - D60x24, 1) + ds
                    End If
                Next
            End If
            e(16) = e(16) - 持続型インスリンオフセット時間
            ds = 0
        ElseIf e(7) = "0" And e(10) = 速攻型インスリン Then
            ds = e(9) * 速攻型インスリンUnit数 / 速攻型インスリン活性持続時間
            e(16) = e(16) + 速攻型インスリンオフセット時間
            If e(16) > D60x24 Then
                ログ出力("ほっとく前々日速攻")
            ElseIf e(16) = D60x24 Then
                ログ出力("ほっとく前々日速攻")
            Else
                For ii = 0 To 速攻型インスリン活性持続時間
                    If e(16) + ii >= D60x24 Then
                        補間インスリンレベル値列前日(e(16) + ii - D60x24, 1) _
                            = 補間インスリンレベル値列前日(e(16) + ii - D60x24, 1) + ds
                    End If
                Next
            End If
            e(16) = e(16) - 速攻型インスリンオフセット時間
            ds = 0
        End If
    End Sub

    Sub データ抽出(
        ByRef ag(,) As Single, ByRef g(,) As Single,
        ByRef ar(,) As Single, ByRef r(,) As Single
    )
        Dim DatCnt As Integer = 0
        Dim i As Integer, j As Integer, k As Integer
        Dim fp As Integer = -3

        For i = 0 To D60x24 + 2
            If ag(i, 1) > -1 Then
                DatCnt = DatCnt + 1
            End If
        Next

        ReDim g(DatCnt - 1, 1)
        ReDim r(DatCnt - 1, 1)

        j = 0
        If ag(0, 1) < 0 Then
            fp = 1
            Console.WriteLine("想定外データ ag(0,1)が未設定　エラー停止させます。returnを押してください。")
            Dim Input As String = Console.ReadLine()
            Dim v = Integer.Parse(Input)
        End If
        For i = 0 To D60x24 + 2
            If ag(i, 1) > -1 Then
                g(j, 0) = ag(i, 0)
                g(j, 1) = ag(i, 1)
                r(j, 0) = ar(i, 0)
                r(j, 1) = ar(i, 1)
                j = j + 1
                If fp > 0 And ((i - fp) > センサ異常判定間隔 Or (i - fp) < -10000) Then
                    If fp > 10000 Then fp -= 100000
                    For k = fp To i - 1
                        ar(k, 1) = -2
                        ag(k, 1) = -2
                    Next
                End If
                fp = -3
            ElseIf ag(i, 1) < -1 Then
                fp = 100000 + i + 1
            Else
                If fp < 0 Then
                    fp = i
                End If
            End If
        Next
        If fp > 0 And (i - fp) > 15 Then
            For k = fp To i - 1
                ar(k, 1) = -2
                ag(k, 1) = -2
            Next
        End If
    End Sub

    Sub 変動解析用傾き分布算出_直近()

        '変動解析用傾き分布抽出（直近）
        Dim i As Integer, j As Integer, kk As Integer
        Dim gx1 As Single, gy1 As Single, gx2 As Single, gy2 As Single
        Dim gp1 As Single, gq1 As Single, gp2 As Single, gq2 As Single
        Dim rx1 As Single, ry1 As Single, rx2 As Single, ry2 As Single
        Dim rp1 As Single, rq1 As Single, rp2 As Single, rq2 As Single

        gy1 = 生Glimp0値列当日(最終計測時刻 + 1, 1) : gx1 = 生Glimp0値列当日(最終計測時刻 + 1, 0)
        ry1 = 生センサ値列当日(最終計測時刻 + 1, 1) : rx1 = gx1
        gq1 = gy1 : gp1 = gx1 : 直近Glimp0値列(4, 0) = gp1 : 直近Glimp0値列(4, 1) = gq1
        rq1 = ry1 : rp1 = rx1 : 直近センサ値列(4, 0) = rp1 : 直近センサ値列(4, 1) = rq1
        If 解析範囲 <= 最終計測時刻 Then ' 00:40 <= 最終計測時刻
            For i = 解析単位 To 解析範囲 Step 解析単位
                j = 最終計測時刻 - i + 1
                gy2 = 生Glimp0値列当日(j, 1) : gx2 = 生Glimp0値列当日(j, 0)
                ry2 = 生センサ値列当日(j, 1) : rx2 = gx2
                dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                If (i Mod 解析単位x2) = 0 Then
                    gp2 = gx2 : gq2 = gy2
                    rp2 = rx2 : rq2 = ry2
                    kk = 4 - i / 解析単位x2
                    dGlimp0値列4(kk) = (gq2 - gq1) / (gp2 - gp1) : 直近Glimp0値列(kk, 0) = gp2 : 直近Glimp0値列(kk, 1) = gq2
                    dセンサ値列4(kk) = (rq2 - rq1) / (rp2 - rp1) : 直近センサ値列(kk, 0) = rp2 : 直近センサ値列(kk, 1) = rq2
                    gp1 = gp2 : gq1 = gq2
                    rp1 = rp2 : rq1 = rq2
                End If
                gx1 = gx2 : gy1 = gy2
                rx1 = rx2 : ry1 = ry2
            Next
        ElseIf 解析単位x2 <= 最終計測時刻 Then '00:10 <= 最終計測時刻 < 00:40
            For i = 解析単位 To 解析範囲 Step 解析単位
                If (最終計測時刻 - i) >= 0 Then
                    j = 最終計測時刻 - i + 1
                    gy2 = 生Glimp0値列当日(j, 1) : gx2 = 生Glimp0値列当日(j, 0)
                    ry2 = 生センサ値列当日(j, 1) : rx2 = gx2
                    dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                    dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                    If (i Mod 解析単位x2) = 0 Then
                        gp2 = gx2 : gq2 = gy2
                        rp2 = rx2 : rq2 = ry2
                        kk = 4 - i / 解析単位x2
                        dGlimp0値列4(kk) = (gq2 - gq1) / (gp2 - gp1) : 直近Glimp0値列(kk, 0) = gp2 : 直近Glimp0値列(kk, 1) = gq2
                        dセンサ値列4(kk) = (rq2 - rq1) / (rp2 - rp1) : 直近センサ値列(kk, 0) = rp2 : 直近センサ値列(kk, 1) = rq2
                        gp1 = gp2 : gq1 = gq2
                        rp1 = rp2 : rq1 = rq2
                    End If
                Else
                    j = D60x24 + 最終計測時刻 - i + 1
                    gy2 = 生Glimp0値列前日(j, 1) : gx2 = 生Glimp0値列前日(j, 0) - D60x24
                    ry2 = 生センサ値列前日(j, 1) : rx2 = gx2
                    dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                    dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                    If (i Mod 解析単位x2) = 0 Then
                        gp2 = gx2 : gq2 = gy2
                        rp2 = rx2 : rq2 = ry2
                        kk = 4 - i / 解析単位x2
                        dGlimp0値列4(kk) = (gq2 - gq1) / (gp2 - gp1) : 直近Glimp0値列(kk, 0) = gp2 : 直近Glimp0値列(kk, 1) = gq2
                        dセンサ値列4(kk) = (rq2 - rq1) / (rp2 - rp1) : 直近センサ値列(kk, 0) = rp2 : 直近センサ値列(kk, 1) = rq2
                        gp1 = gp2 : gq1 = gq2
                        rp1 = rp2 : rq1 = rq2
                    End If
                End If
                gx1 = gx2 : gy1 = gy2
                rx1 = rx2 : ry1 = ry2
            Next
        ElseIf 解析単位 <= 最終計測時刻 Then '00:05 <= 最終計測時刻 < 00:10
            For i = 解析単位 To 解析範囲 Step 解析単位
                If (最終計測時刻 - i) >= 0 Then
                    j = 最終計測時刻 - i + 1
                    gx2 = 生Glimp0値列当日(j, 0) : gy2 = 生Glimp0値列当日(j, 1)
                    dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                    dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                Else
                    j = D60x24 + 最終計測時刻 - i + 1
                    gy2 = 生Glimp0値列前日(j, 1) : gx2 = 生Glimp0値列前日(j, 0) - D60x24
                    ry2 = 生センサ値列前日(j, 1) : rx2 = gx2
                    dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                    dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                    If (i Mod 解析単位x2) = 0 Then
                        gp2 = gx2 : gq2 = gy2
                        rp2 = rx2 : rq2 = ry2
                        kk = 4 - i / 解析単位x2
                        dGlimp0値列4(kk) = (gq2 - gq1) / (gp2 - gp1) : 直近Glimp0値列(kk, 0) = gp2 : 直近Glimp0値列(kk, 1) = gq2
                        dセンサ値列4(kk) = (rq2 - rq1) / (rp2 - rp1) : 直近センサ値列(kk, 0) = rp2 : 直近センサ値列(kk, 1) = rq2
                        gp1 = gp2 : gq1 = gq2
                        rp1 = rp2 : rq1 = rq2
                    End If
                End If
                gx1 = gx2 : gy1 = gy2
                rx1 = rx2 : ry1 = ry2
            Next
        Else '00:00 <= 最終計測時刻 < 00:05
            For i = 解析単位 To 解析範囲 Step 解析単位
                j = D60x24 + 最終計測時刻 - i + 1
                gy2 = 生Glimp0値列前日(j, 1) : gx2 = 生Glimp0値列前日(j, 0) - D60x24
                ry2 = 生センサ値列前日(j, 1) : rx2 = gx2
                dGlimp0値列8(8 - i / 解析単位) = (gy2 - gy1) / (gx2 - gx1)
                dセンサ値列8(8 - i / 解析単位) = (ry2 - ry1) / (rx2 - rx1)
                If (i Mod 解析単位x2) = 0 Then
                    gp2 = gx2 : gq2 = gy2
                    rp2 = rx2 : rq2 = ry2
                    kk = 4 - i / 解析単位x2
                    dGlimp0値列4(kk) = (gq2 - gq1) / (gp2 - gp1) : 直近Glimp0値列(kk, 0) = gp2 : 直近Glimp0値列(kk, 1) = gq2
                    dセンサ値列4(kk) = (rq2 - rq1) / (rp2 - rp1) : 直近センサ値列(kk, 0) = rp2 : 直近センサ値列(kk, 1) = rq2
                    gp1 = gp2 : gq1 = gq2
                    rp1 = rp2 : rq1 = rq2
                End If
                gx1 = gx2 : gy1 = gy2
                rx1 = rx2 : ry1 = ry2
            Next
        End If

    End Sub

    Function 予測() As String()
        Dim i As Integer
        Dim c(2) As Double
        Dim u As Double
        Dim 予測値 As Double = -1
        Dim 予測種別 As String

        ReDim 予測Glimp値列(4, 1)

        u = dGlimp0値列4(3) + dGlimp0値列4(2) + dGlimp0値列4(1) '+ dGlimp0値列4(0)
        u = Math.Abs(u / 3)
        If u > 最小微係数分散 AndAlso dGlimp0値列4(3) <= 0.1 AndAlso dGlimp0値列4(2) <= 0.1 AndAlso dGlimp0値列4(1) <= 0.1 Then 'AndAlso dGlimp0値列4(0) <= 0.1 Then
            予測種別 = MSG低血糖
        ElseIf u > 最小微係数分散 AndAlso dGlimp0値列4(3) >= -0.1 AndAlso dGlimp0値列4(2) >= -0.1 AndAlso dGlimp0値列4(1) >= -0.1 Then 'AndAlso dGlimp0値列4(0) >= -0.1 Then
            予測種別 = MSG高血糖
        Else
            予測種別 = ""
            '予測値 = 100 '正常血糖値
        End If

        If 予測種別 <> "" Then
            Module2.Int二次回帰()
            For i = 0 To 4
                ログ出力(直近Glimp0値列(i, 0) & "," & 直近Glimp0値列(i, 1))
                Module2.addData(直近Glimp0値列(i, 0), 直近Glimp0値列(i, 1))
            Next
            c = Module2.get二次回帰係数
            ログ出力(c(0)) : ログ出力(c(1)) : ログ出力(c(2))
            For i = 0 To 4
                u = 直近Glimp0値列(4, 0) + i * 10
                予測Glimp値列(i, 0) = u
                予測Glimp値列(i, 1) = c(0) * u * u + c(1) * u + c(2)
            Next
            予測値 = 予測Glimp値列(4, 1) : ログ出力(予測値)
        End If

        If Not (予測値 >= 高血糖水準 OrElse 予測値 <= 低血糖水準) Then
            予測種別 = ""
        End If

        Dim ret = {予測種別, 予測値.ToString, 予測Glimp値列(4, 0).ToString}
        Return ret
    End Function

    Sub 変動解析用傾き分布算出_前日()
        '変動解析用傾き分布抽出（前日）
        Dim kg30 As Single, kr30 As Single
        Dim k10(1, 4) As Single
        Dim k05(1, 8) As Single
        Dim i As Integer, j As Integer, ii As Integer
        Dim gy1 As Single, gy2 As Single
        Dim gq1 As Single, gq2 As Single
        Dim ry1 As Single, ry2 As Single
        Dim rq1 As Single, rq2 As Single

        gy1 = 生Glimp0値列前日(5 * 0 + 1, 1) : gq1 = gy1
        ry1 = 生センサ値列前日(5 * 0 + 1, 1) : rq1 = ry1
        For i = 1 To 8
            gy2 = 生Glimp0値列前日(5 * i + 1, 1) : gq2 = gy2
            ry2 = 生センサ値列前日(5 * i + 1, 1) : rq2 = ry2
            k05(0, i) = (gy2 - gy1) / 5
            k05(1, i) = (ry2 - ry1) / 5
            If (i Mod 2) = 0 Then
                gq2 = gy2
                rq2 = ry2
                k10(0, i / 2) = (gq2 - gq1) / 10
                k10(1, i / 2) = (rq2 - rq1) / 10
                gq1 = gq2
                rq1 = rq2
            End If
            gy1 = gy2
            ry1 = ry2
        Next

        For i = 40 To D60x24 - 30 Step 5
            ii = (i - 40) / 5
            '直後30分の増加計算
            kg30 = (生Glimp0値列前日(30 + i + 1, 1) - 生Glimp0値列前日(i + 1, 1)) / 30
            kr30 = (生センサ値列前日(30 + i + 1, 1) - 生センサ値列前日(i + 1, 1)) / 30
            '直近３０分間の一次微係数分布（間隔５分）登録
            a05data(0, ii, 0) = i : a05data(0, ii, 1) = 生Glimp0値列前日(i + 1, 1)
            a05data(1, ii, 0) = i : a05data(1, ii, 1) = 生センサ値列前日(i + 1, 1)
            For j = 3 To 8
                a05data(0, ii, j - 1) = k05(0, j)
                a05data(1, ii, j - 1) = k05(1, j)
            Next
            '直後30分の増加登録
            a05data(0, ii, 8) = kg30
            a05data(1, ii, 8) = kr30
            '直近30分間の一次微係数（間隔5分）更新
            For j = 4 To 8
                k05(0, j - 1) = k05(0, j)
                k05(1, j - 1) = k05(1, j)
            Next
            k05(0, 8) = (生Glimp0値列前日(5 + i + 1, 1) - 生Glimp0値列前日(i + 1, 1)) / 5
            k05(1, 8) = (生センサ値列前日(5 + i + 1, 1) - 生センサ値列前日(i + 1, 1)) / 5

            If (i Mod 10) = 0 Then
                ii = ii / 2
                '直近３０分間の一次微係数分布（間隔５分）登録
                a10data(0, ii, 0) = i : a10data(0, ii, 1) = 生Glimp0値列前日(i + 1, 1)
                a10data(1, ii, 0) = i : a10data(1, ii, 1) = 生センサ値列前日(i + 1, 1)
                For j = 1 To 4
                    a10data(0, ii, j + 1) = k10(0, j)
                    a10data(1, ii, j + 1) = k10(1, j)
                Next
                '直後30分の増加登録
                a10data(0, ii, 6) = kg30
                a10data(1, ii, 6) = kr30
                '直近30分間の一次微係数（間隔10分）更新
                For j = 2 To 4
                    k10(0, j - 1) = k10(0, j)
                    k10(1, j - 1) = k10(1, j)
                Next
                k10(0, 4) = (生Glimp0値列前日(10 + i + 1, 1) - 生Glimp0値列前日(i + 1, 1)) / 10
                k10(1, 4) = (生センサ値列前日(10 + i + 1, 1) - 生センサ値列前日(i + 1, 1)) / 10
            End If
        Next

        If dbgf Then
            Dim txt As String
            ログ出力("------------------------------------------------------------------------------")
            For i = 0 To 144
                txt = a10data(0, i, 0)
                For j = 1 To 4
                    txt = txt + "," + a10data(0, i, j).ToString
                Next
                ログ出力(txt)
            Next
            ログ出力("------------------------------------------------------------------------------")
            For i = 0 To 288
                txt = a05data(0, i, 0)
                For j = 1 To 8
                    txt = txt + "," + a05data(0, i, j).ToString
                Next
                ログ出力(txt)
            Next
            Debug.Print("")
        End If
    End Sub

    Sub 折れ線補間(ByRef ag(,) As Single, ByRef g(,) As Single, ByRef ar(,) As Single, ByRef r(,) As Single, ByRef dg(,) As Single, ByRef dr(,) As Single)
        Dim i As Integer, j As Integer
        Dim gs As Single, gy0 As Single, rs As Single, ry0 As Single, m As Single
        Dim n As Single = 0
        Dim f As Boolean
        Dim dcnt As Integer = 0

        If ag(D60x24 + 2, 1) > -1 Then
            m = D60x24
            n = m
        Else
            m = g(g.Length / 2 - 1, 0)
        End If

        For i = 0 To D60x24 + 2
            dg(i, 0) = ODF - 1 : dr(1, 0) = dg(i, 0)
        Next

        Debug.Print("")
        For i = 0 To g.Length / 2 - 2
            gs = (g(i + 1, 1) - g(i, 1)) / (g(i + 1, 0) - g(i, 0))
            gy0 = g(i, 1) - gs * g(i, 0)
            rs = (r(i + 1, 1) - r(i, 1)) / (r(i + 1, 0) - r(i, 0))
            ry0 = r(i, 1) - rs * r(i, 0)
            f = True
            For j = g(i, 0) To g(i + 1, 0)
                If 0 <= j And j <= m Then
                    If f Then
                        dg(dcnt, 0) = g(i, 0) + Int((g(i + 1, 0) - g(i, 0)) / 2) - n : dg(dcnt, 1) = gs
                        dr(dcnt, 0) = g(i, 0) + Int((g(i + 1, 0) - g(i, 0)) / 2) - n : dr(dcnt, 1) = rs
                        dcnt = dcnt + 1
                        f = False
                    End If
                    If ag(j + 1, 1) > -2 Then
                        ag(j + 1, 1) = gs * j + gy0
                        ar(j + 1, 1) = rs * j + ry0
                    End If
                End If
            Next
        Next

    End Sub

    Sub 変動解析用傾き分布算出_直近2(
        ByRef pdGlimp0値列当日 As Single(,),
        ByRef pdGlimp0値列前日 As Single(,),
        ByRef pdセンサ値列当日 As Single(,),
        ByRef pdセンサ値列前日 As Single(,)
    )

        Dim dGlimp0値列(D60x24 + 2, 1) As Single 'glimp値一次微分列
        Dim dセンサ値列(D60x24 + 2, 1) As Single 'センサ値一次微分列

        Dim i As Integer, j As Integer, k1 As Integer, k2 As Integer
        Dim ss As Single
        Dim fg As Boolean, fr As Boolean

        '変動解析用傾き分布抽出２
        For i = 0 To D60x24 + 2
            dGlimp0値列(i, 0) = ODF - 1
            dセンサ値列(i, 0) = ODF - 1
        Next

        k1 = 0 : k2 = 0
        For i = 0 To D60x24
            If pdGlimp0値列当日(i, 0) < ODF Then
                j = i - 1
                Exit For
            End If
        Next

        fg = True : fr = True
        For i = j To 0 Step -1
            If fg OrElse Math.Abs(pdGlimp0値列当日(i, 1)) >= 有効値 Then
                dGlimp0値列(k1, 0) = pdGlimp0値列当日(i, 0)
                dGlimp0値列(k1, 1) = pdGlimp0値列当日(i, 1)
                If Math.Abs(pdGlimp0値列当日(i, 1)) >= 有効値 Then fg = False
                k1 = k1 + 1
            End If
            If fr OrElse Math.Abs(pdセンサ値列当日(i, 1)) >= 有効値 Then
                dセンサ値列(k2, 0) = pdセンサ値列当日(i, 0)
                dセンサ値列(k2, 1) = pdセンサ値列当日(i, 1)
                If Math.Abs(pdセンサ値列当日(i, 1)) >= 有効値 Then fr = False
                k2 = k2 + 1
            End If
        Next

        For i = 0 To D60x24
            If pdGlimp0値列前日(i, 0) < ODF Then
                j = i - 1
                Exit For
            End If
        Next
        For i = j To 0 Step -1
            If fg OrElse Math.Abs(pdGlimp0値列前日(i, 1)) >= 有効値 Then
                dGlimp0値列(k1, 0) = pdGlimp0値列前日(i, 0)
                dGlimp0値列(k1, 1) = pdGlimp0値列前日(i, 1)
                If Math.Abs(pdGlimp0値列前日(i, 1)) >= 有効値 Then fg = False
                k1 = k1 + 1
            End If
            If fr OrElse Math.Abs(pdセンサ値列前日(i, 1)) >= 有効値 Then
                dセンサ値列(k2, 0) = pdセンサ値列前日(i, 0)
                dセンサ値列(k2, 1) = pdセンサ値列前日(i, 1)
                If Math.Abs(pdセンサ値列前日(i, 1)) >= 有効値 Then fr = False
                k2 = k2 + 1
            End If
        Next

        If dbgf Then
            ss = 0
            j = 0
            For i = 0 To D60x24
                If dGlimp0値列(i, 0) < (dGlimp0値列(0, 0) - 有効範囲) Then Exit For
                ログ出力("t=" & dGlimp0値列(i, 0) & "," & "s=" & dGlimp0値列(i, 1))
                ss = ss + dGlimp0値列(i, 1) : j = dGlimp0値列(i, 0)
            Next
            ss = Math.Round(ss / (dGlimp0値列(0, 0) - j), 7)
            ログ出力("avgs=" & ss)
        End If

        Debug.Print("")
    End Sub

    Sub 補間()
        Dim dGlimp0値列当日(D60x24 + 2, 1) As Single           'glimp値一次微分列当日
        Dim dGlimp0値列前日(D60x24 + 2, 1) As Single           'glimp値一次微分列前日
        Dim dセンサ値列当日(D60x24 + 2, 1) As Single           'センサ値一次微分列当日’
        Dim dセンサ値列前日(D60x24 + 2, 1) As Single           'センサ値一次微分列前日’

        データ抽出(生Glimp0値列当日, 補間Glimp0値列当日, 生センサ値列当日, 補間センサ値列当日)
        折れ線補間(生Glimp0値列当日, 補間Glimp0値列当日, 生センサ値列当日, 補間センサ値列当日, dGlimp0値列当日, dセンサ値列当日)
        データ抽出(生Glimp0値列前日, 補間Glimp0値列前日, 生センサ値列前日, 補間センサ値列前日)
        折れ線補間(生Glimp0値列前日, 補間Glimp0値列前日, 生センサ値列前日, 補間センサ値列前日, dGlimp0値列前日, dセンサ値列前日)

        Call 変動解析用傾き分布算出_直近()
        Call 変動解析用傾き分布算出_直近2(dGlimp0値列当日, dGlimp0値列前日, dセンサ値列当日, dセンサ値列前日)
        Call 変動解析用傾き分布算出_前日()
    End Sub

    Sub 作図本体_補助線(ByRef g As Graphics, ByVal n As Integer, ByVal mgv As Single)
        Dim graphPen As Pen

        graphPen = New Pen(Color.Red, 1)
        graphPen.DashStyle = DashStyle.Dot
        For q1 = 50 To 70 Step 10
            g.DrawLine(graphPen, 0, Int(mgv * (最大Glimp値 - q1)), CType(D60x24 / n, Integer), Int(mgv * (最大Glimp値 - q1)))
        Next
        graphPen = Nothing

        graphPen = New Pen(Color.Yellow, 1)
        graphPen.DashStyle = DashStyle.Dot
        For q1 = 80 To 190 Step 10
            g.DrawLine(graphPen, 0, Int(mgv * (最大Glimp値 - q1)), CType(D60x24 / n, Integer), Int(mgv * (最大Glimp値 - q1)))
        Next
        graphPen = Nothing

        graphPen = New Pen(Color.Yellow, 2)
        graphPen.DashStyle = DashStyle.Dash
        g.DrawLine(graphPen, 0, Int(mgv * (最大Glimp値 - 200)), CType(D60x24 / n, Integer), Int(mgv * (最大Glimp値 - 200)))
        graphPen = Nothing

        graphPen = New Pen(Color.Yellow, 2)
        graphPen.DashStyle = DashStyle.DashDot
        g.DrawLine(graphPen, 0, Int(mgv * (最大Glimp値 - 150)), CType(D60x24 / n, Integer), Int(mgv * (最大Glimp値 - 150)))
        graphPen = Nothing

        graphPen = New Pen(Color.White, 2)
        graphPen.DashStyle = DashStyle.Solid
        g.DrawLine(graphPen, 0, Int(mgv * (最大Glimp値 - 100)), CType(D60x24 / n, Integer), Int(mgv * (最大Glimp値 - 100)))
        graphPen = Nothing

        graphPen = New Pen(Color.White, 1)
        graphPen.DashStyle = DashStyle.Solid
        For q1 = 6 To 18 Step 6
            g.DrawLine(graphPen, _
                CType(60 * q1 / n, Integer), Int(mgv * (最大Glimp値 - 0)), _
                CType(60 * q1 / n, Integer), Int(mgv * (最大Glimp値 - 最大Glimp値)) _
            )
        Next
        For q1 = 1 To 23
            g.DrawLine(graphPen, _
                CType(60 * q1 / n, Integer), Int(mgv * (最大Glimp値 - 100 + SubFLen)), _
                CType(60 * q1 / n, Integer), Int(mgv * (最大Glimp値 - 100 - SubFLen)) _
            )
        Next
        graphPen = Nothing

    End Sub

    Sub インスリンレベルグラフ作成(ByRef gg As Graphics, ByVal n As Integer, ByVal m As Single, ByRef il(,) As Single, ByRef pen1 As Pen, ByRef pen2 As Pen)
        Dim il00 As Single, il01 As Single
        Dim inf As Integer = 0
        il00 = il(1, 0) : il01 = il(1, 1)
        Dim pp() As Point, pp1 As Point, pp2 As Point, pp3 As Point, pp4 As Point

        For i = 2 To D60x24 - 2
            If il01 <> il(i + 0, 1) Then
                gg.DrawLine(pen1, _
                    Int(il00 / n), Int(m * IL_Mg * il01), _
                    Int(il(i - 1, 0) / n), Int(m * IL_Mg * il(i - 1, 1)) _
                )
                gg.DrawLine(pen1, _
                    Int(il(i - 1, 0) / n), Int(m * IL_Mg * il(i - 1, 1)), _
                    Int(il(i - 0, 0) / n), Int(m * IL_Mg * il(i - 0, 1)) _
                )
                If il(i - 1, 1) > TH_Subline Or il(i - 0, 1) >= TH_Subline Then
                    If inf = 0 Then
                        If il(i - 1, 1) < il(i - 0, 1) Then 'inc
                            ' draw subline
                            pp1 = New Point(Int(il(i - 0, 0) / n), Int((最大Glimp値 - 70) * m))
                            pp2 = New Point(Int(il(i - 0, 0) / n), Int((最大Glimp値 - 180) * m))
                            'gg.DrawLine(pen2, pp1, pp2)
                            inf = -1
                        Else 'dec
                            pp1 = New Point(Int(il(1, 0) / n), Int((最大Glimp値 - 70) * m))
                            pp2 = New Point(Int(il(1, 0) / n), Int((最大Glimp値 - 180) * m))
                            pp3 = New Point(Int(il(i - 1, 0) / n), Int((最大Glimp値 - 70) * m))
                            pp4 = New Point(Int(il(i - 1, 0) / n), Int((最大Glimp値 - 180) * m))
                            pp = {pp1, pp2, pp4, pp3}
                            gg.DrawPolygon(pen2, pp)
                            inf = 1
                        End If
                    Else
                        If il(i - 1, 1) < il(i - 0, 1) Then 'inc
                            If inf > 0 Then
                                ' draw subline
                                pp1 = New Point(Int(il(i - 0, 0) / n), Int((最大Glimp値 - 70) * m))
                                pp2 = New Point(Int(il(i - 0, 0) / n), Int((最大Glimp値 - 180) * m))
                                'gg.DrawLine(pen2, pp1, pp2)
                                inf = -1
                            End If
                        Else 'dec
                            If inf < 0 And il(i - 0, 1) <= TH_Subline Then
                                'draw subline
                                pp3 = New Point(Int(il(i - 1, 0) / n), Int((最大Glimp値 - 70) * m))
                                pp4 = New Point(Int(il(i - 1, 0) / n), Int((最大Glimp値 - 180) * m))
                                pp = {pp1, pp2, pp4, pp3}
                                gg.DrawPolygon(pen2, pp)
                                inf = 1
                            End If
                        End If
                    End If
                End If
                il00 = il(i, 0) : il01 = il(i, 1)
            End If
        Next
        gg.DrawLine(pen1, _
            Int(il00 / n), Int(m * IL_Mg * il01), _
            Int(il(D60x24 - 1, 0) / n), Int(m * IL_Mg * il(D60x24 - 1, 1)) _
        )
        If inf < 0 Then
            'draw subline
            pp3 = New Point(Int(il(D60x24, 0) / n), Int((最大Glimp値 - 70) * m))
            pp4 = New Point(Int(il(D60x24, 0) / n), Int((最大Glimp値 - 180) * m))
            pp = {pp1, pp2, pp4, pp3}
            gg.DrawPolygon(pen2, pp)
            inf = 1
        End If
    End Sub

    Sub セーブ・グラフデータ(ByRef bmp As Bitmap, ByVal gFn As String, ByVal fld As String, ByVal n As Integer, ByVal m As Integer)
        Dim fn As String
        fn = gFn & "\graph" & gFn.Substring(InStrRev(gFn, "\")) & "_" & n.ToString & "X" & m.ToString & "Y" & ".bmp"
        If File.Exists(fn) Then
            File.Delete(fn)
        End If
        bmp.Save(fn)
        fn = GRAPH_DIR & fld & n.ToString & "X" & m.ToString & "Y" & ".bmp"
        If File.Exists(fn) Then
            File.Delete(fn)
        End If
        bmp.Save(fn)

        fn = gFn & "\graph" & gFn.Substring(InStrRev(gFn, "\")) & "_" & n.ToString & "X" & m.ToString & "Y" & ".jpg"
        If File.Exists(fn) Then File.Delete(fn)
        'bmp.Save(fn, System.Drawing.Imaging.ImageFormat.Jpeg)
        'fn = GRAPH_DIR & fld & n.ToString & "X" & m.ToString & "Y" & ".jpg"
        fn = DBOX_GLIMPD & fld & n.ToString & "X" & m.ToString & "Y" & ".png"
        If File.Exists(fn) Then
            File.Delete(fn)
        End If
        bmp.Save(fn, System.Drawing.Imaging.ImageFormat.Png)

    End Sub

    Sub 作図本体(
            ByRef d(,) As Single,
            ByVal sm(,) As Single,
            ByVal il(,) As Single,
            ByVal graphFn As String,
            ByVal dfld As String,
            ByVal em(,) As String,
            ByVal ts As String,
            ByVal msg As String
        )
        Dim mgv As Single, ddd As Single
        Dim i As Integer, m As Integer, n As Integer, ofh As Integer, ofw As Integer, q As Integer
        Dim canvas As Bitmap '= New Bitmap(D60x24, 最大Glimp値)
        Dim g As Graphics
        Dim cb As Brush
        Dim graphPen As Pen '= New Pen(Color.Yellow, 2)'Penオブジェクトの作成(幅5の黒色)

        Dim ecnt As Integer = -1
        Dim es As String

        For n = 0 To em.Length / 2 - 1
            If em(n, 0) = "" Then
                ecnt = n
                Exit For
            End If
        Next

        If Not Directory.Exists(graphFn) Then Directory.CreateDirectory(graphFn)

        Dim bc As Brush
        Dim fnt As Font
        Dim sf As StringFormat
        Dim subPen As Pen = New Pen(Color.Tomato, 1)
        subPen.DashStyle = DashStyle.DashDot
        For n = 1 To 3
            For m = 10 To 30 Step mgStep
                mgv = m / 10
                canvas = New Bitmap(CType(D60x24 / n + 1, Integer), CType(最大Glimp値 * mgv + 1, Integer))
                g = Graphics.FromImage(canvas)

                g.FillRectangle(Brushes.Black, g.VisibleClipBounds) '背景を黒で塗りつぶす

                作図本体_補助線(g, n, mgv) '補助線

                graphPen = New Pen(Color.White, 1) : graphPen.DashStyle = DashStyle.DashDot
                インスリンレベルグラフ作成(g, n, mgv, il, graphPen, subPen) 'インスリンレベルグラフ作成
                graphPen = Nothing

                'Glimp値グラフ作成
                graphPen = New Pen(Color.Green, 3) : graphPen.DashStyle = DashStyle.Solid
                For i = 1 To D60x24 - 1
                    If d(i, 1) > 0 And d(i + 1, 1) > 0 Then
                        g.DrawLine(graphPen,
                            Int(d(i + 0, 0) / n), Int(mgv * (最大Glimp値 - If(d(i + 0, 1) > 最大Glimp値, 最大Glimp値, d(i + 0, 1)))),
                            Int(d(i + 1, 0) / n), Int(mgv * (最大Glimp値 - If(d(i + 1, 1) > 最大Glimp値, 最大Glimp値, d(i + 1, 1))))
                        )
                    End If
                Next
                graphPen.Dispose()
                graphPen = Nothing

                '予想値
                If Mid(ts, 3, 1) = ":" AndAlso 予測Glimp値列(0, 1) <> 0 AndAlso 予測Glimp値列(1, 1) <> 0 Then
                    If msg = MSG高血糖 OrElse msg = MSG低血糖 Then
                        graphPen = New Pen(Color.Red, 3)
                    Else
                        graphPen = New Pen(Color.Yellow, 3)
                    End If
                    graphPen.DashStyle = DashStyle.Solid
                    For i = 1 To 4
                        If 予測Glimp値列(i, 0) <= D60x24 Then
                            g.DrawLine(graphPen,
                                Int(予測Glimp値列(i - 1, 0) / n), Int(mgv * (最大Glimp値 - If(予測Glimp値列(i - 1, 1) > 最大Glimp値, 最大Glimp値, 予測Glimp値列(i - 1, 1)))),
                                Int(予測Glimp値列(i + 0, 0) / n), Int(mgv * (最大Glimp値 - If(予測Glimp値列(i + 0, 1) > 最大Glimp値, 最大Glimp値, 予測Glimp値列(i + 0, 1))))
                            )
                        End If
                    Next
                    graphPen.Dispose()
                    graphPen = Nothing
                End If

                '日付・時刻
                If Mid(ts, 3, 1) = ":" Then
                    ofh = 25 : ofw = 55
                Else
                    ofh = 25 : ofw = 117
                End If
                fnt = New Font("MS UI Gothic", 16) 'フォントオブジェクトの作成
                g.DrawString(ts, fnt, Brushes.White, canvas.Width - ofw, canvas.Height - ofh) '文字列を位置(0,0)、青色で表示
                fnt.Dispose()
                fnt = Nothing

                'Event記入
                fnt = New Font("@ＭＳ ゴシック", 16, FontStyle.Bold) 'フォントオブジェクトの作成
                sf = New StringFormat() 'StringFormatを作成
                sf.FormatFlags = StringFormatFlags.DirectionVertical '縦書きにする
                For i = 0 To ecnt - 1
                    es = ""
                    bc = Brushes.White
                    Select Case Left(em(i, 1), 1)
                        Case "1" : es = "←Ｇ" : q = 3
                        Case "2" : es = "←ｇ" : q = 3
                        Case "3" : es = "補食→" : q = -70
                        Case "4" : es = "←食事" : q = 3
                        Case "5" : es = "←運動" : q = 3
                        Case "6" : es = "←薬" : q = 3
                        Case "7" : es = "←抜食" : q = 3
                        Case "8" : es = "←警告" : q = 3 : bc = Brushes.Red
                        Case "9" : es = "→" : bc = Brushes.Yellow 'SMBG催促
                        Case " " : es = "←Ｃ" : q = 3
                    End Select
                    If es <> "" Then
                        If i > 0 AndAlso es = "←警告" AndAlso em(i, 1).Substring(0, 1) = em(i - 1, 1).Substring(0, 1) AndAlso (em(i - 1, 0) - em(i, 0)) < 15 Then '警告連発の場合、←のみ
                            es = es.Substring(0, 1)
                        End If
                        If i = 0 AndAlso d(em(i, 0) + 1, 1) <= 0 Then
                            ddd = d(最終計測時刻 + 1, 1)
                        Else
                            ddd = d(em(i, 0) + 1, 1)
                        End If
                        If es = "→" Then
                            g.DrawString(es, fnt, bc, CType((em(i, 0) - 40) / n, Integer), Int(mgv * (最大Glimp値 - 200)) - 26, sf)
                            'If Mid(ts, 3, 1) = ":" And i = 0 Then ログ出力("wirte eventu " & em(0, 0) & "-" & em(0, 1))
                        Else
                            g.DrawString(es, fnt, bc, CType((em(i, 0) - 40) / n, Integer), Int(mgv * (最大Glimp値 - ddd)) + q, sf)
                            'If Mid(ts, 3, 1) = ":" And i = 0 Then ログ出力("wirte eventu " & em(0, 0) & "-" & em(0, 1))
                        End If
                    End If
                Next
                sf.Dispose()
                sf = Nothing
                fnt.Dispose()
                fnt = Nothing

                'SMBG値PLOT                    
                cb = New SolidBrush(Color.Red)
                For i = 0 To Int(sm.Length / 2) - 1
                    If sm(i, 1) > 0 Then
                        g.FillEllipse(cb, CType(sm(i, 0) / n, Integer) - SMBG_PCR, Int(mgv * (最大Glimp値 - sm(i, 1))) - SMBG_PCR, 2 * SMBG_PCR, 2 * SMBG_PCR)
                    End If
                Next
                cb.Dispose()
                cb = Nothing

                セーブ・グラフデータ(canvas, graphFn, dfld, n, m)

                'リソースを解放する
                g.Dispose()
                canvas.Dispose()
                canvas = Nothing
            Next
        Next
        subPen = Nothing
        canvas = Nothing
    End Sub

    Sub 作図(ByVal 予測 As String())
        作図本体(
            生Glimp0値列当日,
            smbg当日,
            補間インスリンレベル値列当日,
            graphFn当日,
            "当日\",
            Event当日,
            str最終計測時刻,
            予測(0)
        )
        作図本体(
            生Glimp0値列前日,
            smbg前日,
            補間インスリンレベル値列前日,
            graphFn前日,
            "前日\",
            Event前日,
            str前日日付.Substring(2),
        予測(0)
        )
    End Sub

    Function GetEventAndResetEvent当日Event当日() As String()
        Dim i As Integer, j As Integer
        Dim lines As String()
        Dim e As String()
        Dim stk = New Stack

        For i = 0 To 最大イベント数
            Event当日(i, 0) = "" : Event当日(i, 1) = ""
            Event前日(i, 0) = "" : Event前日(i, 1) = ""
        Next

        i = 0 : j = 0
        lines = File.ReadAllLines(DBOX_GLIMPD_EVENT, Encoding.GetEncoding("shift-jis"))
        For Each line In lines
            If line.StartsWith(str当日日付) Then
                e = line.Split(",")
                Event当日(i, 0) = e(16) : Event当日(i, 1) = e(13) : i += 1

            ElseIf line.StartsWith(str前日日付) Then
                e = line.Split(",")
                e = line.Split(",")
                Event前日(j, 0) = e(16) : Event前日(j, 1) = e(13) : j += 1
            Else
                Exit For
            End If
        Next
        Return lines
    End Function

    Sub UpdateEventAndResetEvent当日Event当日(
        ByVal lines As String(),
        ByVal cnt As Integer,
        ByVal m As String()
    )
        Dim j As Integer
        Dim k As Integer = 0
        Dim e As String()
        Dim dt As String()
        Dim lines2(lines.Length + cnt) As String

        If m(1) <> "" Then
            dt = Module2.getTstmp
            lines2(k) = "4," & dt(0) & ":00,,,,,0,,,,,,9" & m(1) & "," & dt(1) : k += 1 'イベントファイル先頭書き込み
        End If
        If m(0) <> "" Then
            If m(1) <> "" Then System.Threading.Thread.Sleep(61000)
            dt = Module2.getTstmp
            lines2(k) = "4," & dt(0) & ":00,,,,,0,,,,,,8" & m(0) & "," & dt(1) : k += 1 'イベントファイル先頭書き込み
        End If

        For j = lines.Length - 1 To 0 Step -1
            lines2(j + cnt) = lines(j)
            Event当日(j + cnt, 0) = Event当日(j, 0)
        Next

        File.WriteAllLines(DBOX_GLIMPD_EVENT, lines2, Encoding.GetEncoding("shift-jis"))

        For j = 0 To cnt - 1
            e = lines2(j).Split(",")
            Event当日(j, 0) = e(16) : Event当日(j, 1) = e(13)
            ログ出力("add new event " & j & "-" & e(13))
        Next

        For j = 0 To 最大イベント数
            If Event当日(j, 0) = "" Then Exit For
            ログ出力(Event当日(j, 0) & " " & Event当日(j, 1))
        Next

    End Sub

    Sub Lineメッセージ送信(ByVal msg As String)
        'set message to clipboard
        th = New System.Threading.Thread(AddressOf SetStr2Clipboard)
        th.SetApartmentState(System.Threading.ApartmentState.STA)
        th.Start(msg)
        th.Join()

        proc = System.Diagnostics.Process.Start(CMD_LINEメッセージ送信) ' send line message
        proc.WaitForExit(10000)                                         ' 待機する時間を指定（10秒だけ）して待つ
        If (proc.HasExited = False) Then                                ' 外部コマンドが終了しているか確認する
            Debug.Print("NG")
        End If
    End Sub

    Sub イベント更新(ByVal 予測 As String())
        Dim 予測種別 = 予測(0)
        Dim 予測値 = Double.Parse(予測(1))
        Dim 予測値の時刻 = Math.Round(Single.Parse(予測(2)), 0)
        Dim msg As String() = {"", "", ""}
        Dim msgcnt As Integer = 0

        If 予測種別 <> "" AndAlso
         ((予測値 >= 高血糖水準 AndAlso 直近Glimp0値列(4, 1) > 高血糖通知水準) OrElse
          (予測値 <= 低血糖水準 AndAlso 直近Glimp0値列(4, 1) < 低血糖通知水準)) Then
            msg(0) = 予測種別 & " " & Math.Round(直近Glimp0値列(4, 1), 1) & "->" & Math.Round(予測値, 1) & " #" & 予測値の時刻 : msgcnt += 1
            Lineメッセージ送信(msg(0))
        End If

        Dim tt = Now.Ticks
        If (tt - LastSmbg) > SMBG通知間隔 AndAlso (tt - SMBG前回催促) > SMBG催促間隔 Then
            msg(1) = SMBG催促MSG : msgcnt += 1 '"血糖値校正のためSMBGして下さい"
            Lineメッセージ送信(msg(1))
            SMBG前回催促 = tt
        End If

        Dim lines = GetEventAndResetEvent当日Event当日()

        If msgcnt > 0 Then UpdateEventAndResetEvent当日Event当日(lines, msgcnt, msg)

    End Sub

    Sub bak01()
        'For i = 0 To lines.Length - 1
        '    lines(i) = ssv2csv(lines(i))
        '    e = lines(i).Split(",")
        '    If i = 0 Then                                       '最新（１行目）のデータ
        '        Debug.Print("start " & e(1))
        '        strDat(0) = e(1)
        '        当日LineConv(e)
        '        didx = 0
        '    Else                                                '２行目以降
        '        If didx = 0 Then                                '当日データ処理
        '            If e(1) = strDat(0) Then
        '                Debug.Print("add dline1")
        '                当日LineConv(e)
        '            Else                                        '当日から前日に切り替わる　前日最後のデータ
        '                Debug.Print("chg 0 to 1 " & e(1))
        '                strDat(1) = e(1)
        '                前日LineConv(e)
        '                didx = 1
        '            End If
        '        ElseIf didx = 1 Then                            '前日データ処理
        '            If e(1) = strDat(1) Then
        '                前日LineConv(e)
        '            Else
        '                Debug.Print("chg 1 to 2 " & e(1))
        '                strDat(2) = e(1)
        '                前々日LineConv(e)
        '                didx = 2
        '            End If
        '        ElseIf didx = 2 Then
        '            If e(1) = strDat(2) Then
        '                前々日LineConv(e)
        '            Else
        '                Debug.Print("chg 2 to 3 " & e(1))
        '                didx = 3
        '            End If
        '        Else
        '            Debug.Print("前前前日以前はスルーする")
        '            Exit For
        '        End If
        '    End If
        '    If f And Not (lines(i).StartsWith(strLast)) Then
        '        If addLines = "" Then
        '            addLines = lines(i)
        '        Else
        '            addLines = lines(i) + ";" + addLines
        '        End If
        '    Else
        '        f = False
        '    End If
        '    If True Then 'dbgf Then
        '        If i Mod 1000 = 0 Then
        '            ログ出力(i)
        '        End If
        '    End If
        'Next
    End Sub

    Sub 本処理()

        Dim i As Integer
        Dim textFile As String
        Dim enc As Encoding
        Dim line As String
        Dim lines As String()
        Dim all_lines As String = ""
        Dim e As String()
        Dim strLast As String
        Dim addLines As String = ""
        Dim f As Boolean = True

        ファイル解凍()
        配列初期化()

        textFile = convCsv & ".next.txt"                        '読み込むテキストファイル名
        enc = Encoding.GetEncoding(OENC)                        '文字コード
        lines = File.ReadAllLines(textFile, enc)
        strLast = Left(lines(0), 18)

        textFile = utf16Csv                                     '読み込むテキストファイル名
        enc = Encoding.GetEncoding("utf-16")                    '文字コード(ここでは、UTF-16)
        lines = File.ReadAllLines(textFile, enc)                '行ごとの配列として、テキストファイルの中身をすべて読み込む

        Dim strDat(2) As String
        Dim didx As Integer = 0
        i = -1
        Using sr As StreamReader = New StreamReader(utf16Csv, Encoding.GetEncoding("utf-16"))
            line = sr.ReadLine() : i = i + 1
            Do Until line Is Nothing
                line = ssv2csv(line) : all_lines &= (line & ";")
                e = line.Split(",")
                If i = 0 Then                                       '最新（１行目）のデータ
                    Debug.Print("start " & e(1))
                    strDat(0) = e(1)
                    当日LineConv(e)
                    didx = 0
                Else                                                '２行目以降
                    If didx = 0 Then                                '当日データ処理
                        If e(1) = strDat(0) Then
                            Debug.Print("add dline1")
                            当日LineConv(e)
                        Else                                        '当日から前日に切り替わる　前日最後のデータ
                            Debug.Print("chg 0 to 1 " & e(1))
                            strDat(1) = e(1)
                            前日LineConv(e)
                            didx = 1
                        End If
                    ElseIf didx = 1 Then                            '前日データ処理
                        If e(1) = strDat(1) Then
                            前日LineConv(e)
                        Else
                            Debug.Print("chg 1 to 2 " & e(1))
                            strDat(2) = e(1)
                            前々日LineConv(e)
                            didx = 2
                        End If
                    ElseIf didx = 2 Then
                        If e(1) = strDat(2) Then
                            前々日LineConv(e)
                        Else
                            Debug.Print("chg 2 to 3 " & e(1))
                            didx = 3
                        End If
                    Else
                        Debug.Print("前前前日以前はスルーする")
                        Exit Do
                    End If
                End If
                If f And Not (line.StartsWith(strLast)) Then
                    If addLines = "" Then
                        addLines = line
                    Else
                        addLines = line + ";" + addLines
                    End If
                Else
                    f = False
                End If
                If True Then 'dbgf Then
                    If i Mod 1000 = 0 Then
                        ログ出力(i)
                    End If
                End If
                line = sr.ReadLine() : i = i + 1
            Loop
        End Using

        'bak01()
        補間()
        Dim 予測結果 = 予測()
        イベント更新(予測結果)
        作図(予測結果)

        enc = Encoding.GetEncoding(OENC)               '文字コード

        '文字コード変換（utf-16 -> utf-8）して保存
        textFile = convCsv                             '書き込み先のテキストファイル名
        File.WriteAllLines(textFile, lines, enc)       'ファイルが存在しているときは、上書きする 

        '先頭行保存
        textFile = convCsv & ".next.txt"               '書き込み先のテキストファイル名
        Dim lines0() As String = {lines(0)}
        File.WriteAllLines(textFile, lines0, enc)      'ファイルが存在しているときは、上書きする 

        '順時系列保存
        Dim revlog As StreamWriter =
            New StreamWriter(DOC_OUT_FULL & ".rev.log", True, Encoding.GetEncoding("shift-jis"))
        revlog.AutoFlush = True
        e = addLines.Split(";")
        For i = 0 To e.Length - 1
            revlog.WriteLine(e(i))
        Next
        revlog.Close()

        分析用ファイル出力(lines)
        連携ファイル出力()

        If Not File.Exists("C:\var\stop_imgUpload.txt") Then
            MyFtpUpload(b_graphs)
        End If

        メール送信("血糖値", str最終計測時刻 & "  " & str最終計測血糖値 & "(mg/dL)")

        If Not dbgf Then
            File.Delete(DBOX_GLIMPD_CONV)
            File.Copy(convCsv, DBOX_GLIMPD_CONV)
            File.Delete(DOC_OUT_FULL)
            File.Copy(convCsv, DOC_OUT_FULL)
            File.Delete(DOC_OUT_FULL & ".txt")
            File.Move(DOC_OUT_FULL & ".next.txt", DOC_OUT_FULL & ".txt")
            File.Copy(convCsv & ".next.txt", DOC_OUT_FULL & ".next.txt", True)
        End If

    End Sub

    Sub 分析用ファイル出力(ByVal data As String())
        Const DM = "?"
        Dim i As Integer, j As Integer
        Dim textfile As String, txt As String
        Dim lines As String()
        Dim enc = Encoding.GetEncoding("shift-jis")

        textfile = graphFn前日 & "\GlimpData.csv"      '書き込み先のテキストファイル名
        If Not File.Exists(textfile) Then
            File.WriteAllLines(textfile, data, enc)
        End If

        textfile = graphFn前日 & "\a10_GlimpData.csv"  '書き込み先のテキストファイル名
        If Not File.Exists(textfile) Then
            ReDim lines(144)
            For i = 0 To 137
                txt = a10data(0, i, 0)
                For j = 1 To 4
                    txt = txt + "," + a10data(0, i, j).ToString
                Next
                lines(i) = txt
            Next
            File.WriteAllLines(textfile, lines, enc)
        End If

        textfile = graphFn前日 & "\a05_GlimpData.csv"  '書き込み先のテキストファイル名
        If Not File.Exists(textfile) Then
            ReDim lines(288)
            For i = 0 To 274
                txt = a05data(0, i, 0)
                For j = 1 To 8
                    txt = txt + "," + a05data(0, i, j).ToString
                Next
                lines(i) = txt
            Next
            File.WriteAllLines(textfile, lines, enc)
        End If

        textfile = graphFn前日 & "\chkPredict.txt"  '書き込み先のテキストファイル名
        If Not File.Exists(textfile) Then
            txt = ""
            For i = 0 To 最大イベント数
                If Event前日(i, 0) = "" Then Exit For
                If Event前日(i, 1)(0) <> "9" Then
                    If Event前日(i, 1)(0) = "8" Then
                        j = Integer.Parse(Event前日(i, 1).Substring(Event前日(i, 1).LastIndexOf("#") + 1))
                        Debug.Print(Event前日(i, 0) & "," & 生Glimp0値列前日(Event前日(i, 0) + 1, 1) & "," & Event前日(i, 1) & "," & 生Glimp0値列前日(j + 1, 1))
                        txt = Event前日(i, 0) & "," & Event前日(i, 1) & "=" & 生Glimp0値列前日(j + 1, 1) & DM & txt
                    Else
                        txt = Event前日(i, 0) & "," & Event前日(i, 1) & DM & txt
                    End If
                End If
            Next
            lines = txt.Split(DM)
            File.WriteAllLines(textfile, lines, enc)
        End If

    End Sub

    Sub 連携ファイル出力()
        Const DM = "?"
        Dim s1 As String
        Dim sws As StreamWriter

        sws = New StreamWriter(直近データ列ファイル, False, Encoding.GetEncoding("shift_jis"))
        sws.AutoFlush = False
        sws.WriteLine(直近Glimp0値列(0, 0) & "," & 直近Glimp0値列(0, 1) & ",-")
        For i = 1 To 4
            sws.WriteLine(直近Glimp0値列(i, 0) & "," & 直近Glimp0値列(i, 1) & "," & dGlimp0値列4(i - 1))
        Next
        sws.Close()
        sws = Nothing

        s1 = 生Glimp0値列当日(1, 1)
        For i = 2 To 1441
            s1 &= ("," + 生Glimp0値列当日(i, 1).ToString)
        Next
        sws = New StreamWriter(当日血糖値列ファイル, False, Encoding.GetEncoding("shift_jis"))
        sws.Write(s1)
        sws.Close()
        sws = Nothing

        s1 = 生Glimp0値列前日(1, 1)
        sws = New StreamWriter(前日血糖値列ファイル, False, Encoding.GetEncoding("shift_jis"))
        For i = 2 To 1441
            s1 &= ("," + 生Glimp0値列前日(i, 1).ToString)
        Next
        sws.Write(s1)
        sws.Close()
        sws = Nothing

        If Not File.Exists(警告検証ファイル) Then
            Dim i As Integer, j As Integer
            Dim txt = ""
            Dim lines As String()
            For i = 0 To 最大イベント数
                If Event前日(i, 0) = "" Then Exit For
                If Event前日(i, 1)(0) <> "9" Then
                    If Event前日(i, 1)(0) = "8" Then
                        j = Integer.Parse(Event前日(i, 1).Substring(Event前日(i, 1).LastIndexOf("#") + 1))
                        Debug.Print(Event前日(i, 0) & "," & 生Glimp0値列前日(Event前日(i, 0) + 1, 1) & "," & Event前日(i, 1) & "," & 生Glimp0値列前日(j + 1, 1))
                        txt = Event前日(i, 0) & "," & Event前日(i, 1) & "=" & 生Glimp0値列前日(j + 1, 1) & DM & txt
                    Else
                        txt = Event前日(i, 0) & "," & Event前日(i, 1) & DM & txt
                    End If
                End If
            Next
            lines = txt.Split(DM)
            File.WriteAllLines(警告検証ファイル, lines, Encoding.GetEncoding("shift-jis"))
        End If

    End Sub

    Sub ログ出力(ByVal s As String)
        sw.WriteLine(s)
        Console.WriteLine(s)
    End Sub

    Sub 監視開始()
        watcher.Path = "C:\Users\hiro\Dropbox\アプリ\Glimp"           '監視するディレクトリを指定
        watcher.Filter = ""                                           '*.txtファイルを監視、すべて監視するときは""にする
        watcher.NotifyFilter =
            System.IO.NotifyFilters.FileName Or
            System.IO.NotifyFilters.DirectoryName Or
            System.IO.NotifyFilters.LastWrite                         'ファイル名とディレクトリ名と最終書き込む日時の変更を監視
        watcher.IncludeSubdirectories = False                         'サブディレクトリは監視しない

    End Sub

    Sub Main()
        Dim XT As Int64 = 10000000
        SMBG通知間隔 *= (3600 * XT)
        SMBG催促間隔 *= (3600 * XT)

        If File.Exists(wDir + "watching.gz") Then dbgf = True Else dbgf = False

        'psi = New ProcessStartInfo() 'ProcessStartInfoオブジェクトを作成する
        'psi.WindowStyle = ProcessWindowStyle.Minimized

        sw = New StreamWriter(Log_File, True, Encoding.GetEncoding("shift_jis")) 'Logファイルの末尾に追加する
        sw.AutoFlush = True

        If dbgf Then
            ダミー主処理呼び出し()
            sw.Close() '閉じる
            Exit Sub
        End If

        Dim l0 As Int64 = 0
        Dim Err_f As Boolean = 必須ファイルOrg_Anal_Next_存在チェック()
        監視開始()
        メール送信("通知", Now.ToString & " 監視開始")
        Dim d1 = File.GetLastWriteTime(DBOX_GLIMPD_GZ_UTF16)
        Dim d2 = File.GetLastWriteTime(DBOX_GLIMPD_CONV)
        If d1 > d2 Then
            ログ出力("Update Start " & d1.ToString & "," & d2.ToString)
            本処理()
        End If
        Do While File.Exists(watcher.Path & "\" & QuitFile) AndAlso Err_f
            l0 = 更新検出および主処理起動(l0)
            If l0 < 0 Then
                Exit Sub
            End If
            'Err_f = 必須ファイルOrg_Anal_Next_存在チェック()
            'If Err_f Then
            '    l0 = 更新検出および主処理起動(l0)
            '    If l0 < 0 Then
            '        Exit Sub
            '    End If
            'Else
            '    System.Threading.Thread.Sleep(200)
            '    Err_f = 必須ファイルOrg_Anal_Next_存在チェック()
            '    If Err_f Then
            '        l0 = 更新検出および主処理起動(l0)
            '        If l0 < 0 Then
            '            Exit Sub
            '        End If
            '    Else
            ログ出力("file check " &
                File.Exists(DBOX_GLIMPD_GZ_UTF16) & "," &
                File.Exists(DBOX_GLIMPD_CONV) & "," &
                File.Exists(DOC_OUT_FULL & ".next.txt")
            )
            Err_f = 必須ファイルOrg_Anal_Next_存在チェック()
            '    End If
            'End If
        Loop

        sw.Close() '閉じる

        メール送信("通知", Now.ToString & " 監視終了")

    End Sub

    Function 更新検出および主処理起動(ByVal ll0 As Int64) As Int64
        Dim changedResult As WaitForChangedResult
        Dim ll1 As Int64 = ll0

        watcher.EnableRaisingEvents = True
        changedResult = watcher.WaitForChanged(WatcherChangeTypes.All, 24 * 3600 * 1000)
        ログ出力(changedResult.Name & " updated")
        If changedResult.TimedOut Then
            ログ出力("タイムアウト終了します。")
            ll0 = -1
        ElseIf changedResult.Name = QuitFile Then
            ログ出力("終了します。")
            ll0 = -2
        ElseIf changedResult.Name = "GlicemiaMisurazioniEvent.csv.gz" Then
            watcher.EnableRaisingEvents = False
            ログ出力("Update Start by event")
            System.Threading.Thread.Sleep(1000)
            本処理()
        ElseIf changedResult.Name = "GlicemiaMisurazioni.csv.gz" Then
            watcher.EnableRaisingEvents = False
            System.Threading.Thread.Sleep(1000)
            Dim d1 = File.GetLastWriteTime(DBOX_GLIMPD_GZ_UTF16)
            Dim d2 = File.GetLastWriteTime(DBOX_GLIMPD_CONV)
            If d1 > d2 Then
                ログ出力("Update Start " & d1.ToString & "," & d2.ToString)
                本処理()
            Else
                Debug.Print("skip")
            End If
        End If

        'll1 = Now().Ticks
        'If (ll1 - ll0) > 10000000 And (changedResult.Name <> QuitFile) Then '10000000=1sec
        '    ログ出力(changedResult.Name & "-" & Now() & "更新開始。")
        '    If changedResult.Name = "GlicemiaMisurazioniEvent.csv.gz" Then
        '        ログ出力("Update Start by event")
        '        本処理()
        '    Else
        '        System.Threading.Thread.Sleep(5000)
        '        Dim d1 = File.GetLastWriteTime(DBOX_GLIMPD_GZ_UTF16)
        '        Dim d2 = File.GetLastWriteTime(DBOX_GLIMPD_CONV)
        '        If d1 > d2 Then
        '            ログ出力("Update Start " & d1.ToString & "," & d2.ToString)
        '            本処理()
        '        Else
        '            Debug.Print("skip")
        '        End If
        '    End If
        'End If
        'll0 = ll1
        'watcher.EnableRaisingEvents = True
        'changedResult = watcher.WaitForChanged(WatcherChangeTypes.All, 24 * 3600 * 1000)
        'If changedResult.TimedOut Then
        '    ログ出力("タイムアウトしました。")
        '    ll0 = -1
        'End If
        'ログ出力(changedResult.Name & " updated")
        'watcher.EnableRaisingEvents = False
        Return ll1
    End Function

    Function 必須ファイルOrg_Anal_Next_存在チェック() As Boolean
        Return File.Exists(DBOX_GLIMPD_GZ_UTF16) AndAlso File.Exists(DBOX_GLIMPD_CONV) AndAlso File.Exists(DOC_OUT_FULL & ".next.txt")
    End Function

    Sub メール送信(ByVal ttl As String, ByVal txt As String)
        Dim s As String, pw As String
        Select Case ttl
            Case "警告"
                s = "2"
                pw = "kZ$67Ysf"
            Case Else
                s = "1"
                pw = "75$ZT5n1"
        End Select

        Dim tadr = "flibrehm48@gmail.com"
        Dim fadr = "alarm1000" & s & "@hypoglycemia.email"

        Dim msg As New System.Net.Mail.MailMessage(fadr, tadr, ttl, txt)

        Dim sc As New System.Net.Mail.SmtpClient()
        sc.Host = "smtp.hypoglycemia.email" 'SMTPサーバーなどを設定する
        sc.Port = 587
        sc.DeliveryMethod = System.Net.Mail.SmtpDeliveryMethod.Network
        sc.Credentials = New System.Net.NetworkCredential(fadr, pw) 'ユーザー名とパスワードを設定する
        sc.Send(msg) 'メッセージを送信する

        msg.Dispose() '後始末
        sc.Dispose() '後始末（.NET Framework 4.0以降）

    End Sub

    Sub MyFtpUpload(ByVal path As String(,))
        Dim buf(1024) As Byte
        Dim i As Integer, count As Integer = 0
        Dim si = New NetworkCredential(FTPID, FTPPW)
        Dim ftpReq As FtpWebRequest

        path(0, 1) = "Data/TODAY/" & WEBGRAH
        path(1, 1) = "Data/" & str当日日付.Substring(2, 4) & "/" & str当日日付.Substring(2, 10).Replace("/", "-") & "_" & smbg_idx0 & "_" & WEBGRAH
        path(2, 1) = "Data/" & str前日日付.Substring(2, 4) & "/" & str前日日付.Substring(2, 10).Replace("/", "-") & "_" & smbg_idx1 & "_" & WEBGRAH
        Try
            For i = 0 To path.Length / 2 - 1
                ftpReq = CType(WebRequest.Create(New Uri(FTPSVR & path(i, 1))), FtpWebRequest) 'FtpWebRequestの作成
                ftpReq.Credentials = si                                                        'ログインユーザー名とパスワードを設定
                ftpReq.Method = WebRequestMethods.Ftp.UploadFile                               'MethodにWebRequestMethods.Ftp.UploadFile("STOR")を設定
                ftpReq.KeepAlive = False                                                       '要求の完了後に接続を閉じる
                ftpReq.UseBinary = True                                                        'ASCIIモードで転送する
                ftpReq.UsePassive = False                                                      'PASVモードを無効にする
                Using st As Stream = ftpReq.GetRequestStream()
                    Using fs As New FileStream(path(i, 0), FileMode.Open)
                        Do
                            count = fs.Read(buf, 0, buf.Length)
                            st.Write(buf, 0, count)
                        Loop While count <> 0
                    End Using
                End Using
                Using ftpRes As FtpWebResponse = CType(ftpReq.GetResponse(), FtpWebResponse)   'FtpWebResponseを取得
                    ログ出力(ftpRes.StatusCode & "," & ftpRes.StatusDescription)               'FTPサーバーから送信されたステータスを表示
                End Using
            Next
        Catch ex As Exception
            ログ出力(ex.ToString)
        End Try
    End Sub

End Module
