using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using Timer = System.Windows.Forms.Timer;
using File = System.IO.File;

#nullable disable

namespace OLEDSaver
{
    public class MonitorSettings
    {
        public string DeviceName { get; set; } = string.Empty;
        public bool Enabled { get; set; } = true;
        public int TimeoutSeconds { get; set; } = 25;
        public string DisplayName { get; set; } = string.Empty;
    }

    static class Program
    {
        private const uint RDW_INVALIDATE = 0x0001;
        private const uint RDW_UPDATENOW = 0x0100;
        private const uint RDW_ALLCHILDREN = 0x0080;
        private const uint EVENT_SYSTEM_FOREGROUND = 0x0003;
        private const uint WINEVENT_OUTOFCONTEXT = 0x0000;
        private const uint SPIF_SENDCHANGE = 0x02;
        private const uint GA_ROOT = 2;
        private const uint THREAD_SET_INFORMATION = 0x0020;
        private const uint THREAD_QUERY_INFORMATION = 0x0040;
        private const int THREAD_PRIORITY_IDLE = -15;
        private const int WM_SYSCOMMAND = 0x0112;
        private const int SC_MONITORPOWER = 0xF170;
        private const int SM_CXSCREEN = 0;
        private const int SM_CYSCREEN = 1;
        private const int SW_HIDE = 0;
        private const int SW_SHOW = 5;
        private const int SPI_GETWORKAREA = 0x0030;
        private const int SPI_SETWORKAREA = 0x002F;
        private const int ENUM_CURRENT_SETTINGS = -1;
        private const int DWMWA_EXTENDED_FRAME_BOUNDS = 9;
        private static readonly IntPtr HWND_BROADCAST = new IntPtr(0xFFFF);

        private static Timer _edgeTimer;
        private static Timer _inactivityTimer;
        private static Point _lastCursorPos = Point.Empty;
        private static DateTime _lastActiveTime = DateTime.Now;
        private static readonly TimeSpan InactivityThreshold = TimeSpan.FromSeconds(1);
        private static DateTime _lastWindowsKeyTime = DateTime.MinValue;
        private static readonly TimeSpan _winKeyShowDuration = TimeSpan.FromSeconds(3);
        private static bool _enableInterpolation = true;
        private static Rectangle _previousTargetRect = Rectangle.Empty;
        private static Rectangle _lastWindowBounds = Rectangle.Empty;
        private static Rectangle _lastActiveWindowRect = Rectangle.Empty;
        private static Rectangle _targetActiveWindowRect = Rectangle.Empty;
        private static Rectangle _currentActiveWindowRect = Rectangle.Empty;
        private static Rectangle _lastRenderedOverlayRect = Rectangle.Empty;
        private static bool _drawBlackOverlay = false;
        private static bool _taskbarHidingEnabled = true;
        private static bool _desktopIconsHidingEnabled = true;
        private static bool _screenOffEnabled = true;
        private static bool _overlayFaded = false;
        private static bool _isVideoPlaying = false;
        private static bool _desktopIconsHidden = false;
        private static bool _drawBlackOverlayEnabled = false;
        private static bool _taskbarHidden = false;
        private static bool _screenOff = false;
        private static int _displayOffTimeoutSeconds = 60;
        private static int _desktopIconsTimeoutSeconds = 3;
        private static int _drawBlackOverlayEnabledTimeoutSeconds = 2;
        private static int _taskbarTimeoutSeconds = 1;
        public static int _activityThreshold = 130;
        private static IntPtr _windowThatTriggeredOverlay = IntPtr.Zero;
        private static bool _overlayRoundedCorners = true;
        private static double _overlayOpacity = 0.93;
        private static double _overlayFadedOpacity = 0.6;
        private static RECT _originalWorkArea;
        private static bool _workAreaStored = false;
        private static NotifyIcon _trayIcon;
        private static CancellationTokenSource _overlayUpdateCts;
        private static ContextMenuStrip _contextMenu;
        private static Dictionary<Screen, Form> _overlays = new();
        private static Dictionary<string, MonitorSettings> _monitorSettings = new();
        private static IntPtr _hookHandle = IntPtr.Zero;
        private static WinEventDelegate _winEventProc = WinEventProc;
        private static List<string> _excludedWindowTitles = new();
        private static DateTime _lastTaskbarInteractionTime = DateTime.MinValue;
        private static readonly string StartupFolderPath = Environment.GetFolderPath(Environment.SpecialFolder.Startup);
        private static readonly string ShortcutPath = Path.Combine(StartupFolderPath, "OLEDSaver.lnk");
        private const string TrayIconResourceName = "OLEDSaver.Resources.OledSaverIcon";

        private static readonly string[] _videoApps =
        {
            "chrome", "firefox", "edge", "opera", "brave",
            "vivaldi", "yandex", "browser", "thorium", "mercury",
            "vlc", "mpc", "potplayer", "kmplayer", "gom", "mpv",
            "wmplayer", "quicktime", "realplayer", "winamp", "foobar",
            "aimp", "smplayer", "bsplayer", "cyberlink", "powerdvd",
            "media player", "videowindowclass", "vlcvideohwnd",
            "youtube", "twitch", "netflix", "hulu", "prime video",
            "disney", "hbo", "paramount", "peacock", "crunchyroll",
            "funimation", "vimeo", "dailymotion", "tiktok", "itunes",
            "premiere", "vegas", "davinci", "camtasia", "filmora",
            "after effects", "avid", "final cut",
            "zoom", "teams", "whatsapp", "viber", "hangouts", "meet", "webex", "gotomeeting",
            "kodi", "plex", "emby", "jellyfin", "media center",
            "xbmc", "mediaportal"
        };

        private static readonly string[] _videoTitleIndicators =
        {
            "playing", "paused", "buffering", "live", "stream",
            "video", "movie", "film", "episode", "season",
            "watch", "player", "▶", "⏸", "⏯", "●", "🔴",
            "воспроизведение", "пауза", "прямой эфир", "стрим"
        };

        private delegate bool EnumWindowsProc(IntPtr hWnd, IntPtr lParam);
        private delegate void WinEventDelegate(IntPtr hWinEventHook, uint eventType,
            IntPtr hwnd, int idObject, int idChild, uint dwEventThread, uint dwmsEventTime);
        private delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);

        [StructLayout(LayoutKind.Sequential)]
        private struct POINT
        {
            public int x, y;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct MSLLHOOKSTRUCT
        {
            public POINT pt;
            public uint mouseData;
            public uint flags;
            public uint time;
            public IntPtr dwExtraInfo;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct RECT
        {
            public int Left;
            public int Top;
            public int Right;
            public int Bottom;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct APPBARDATA
        {
            public int cbSize;
            public IntPtr hWnd;
            public uint uCallbackMessage;
            public uint uEdge;
            public RECT rc;
            public int lParam;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct LASTINPUTINFO
        {
            public uint cbSize;
            public uint dwTime;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct WINDOWPLACEMENT
        {
            public int length;
            public int flags;
            public int showCmd;
            public POINT ptMinPosition;
            public POINT ptMaxPosition;
            public RECT rcNormalPosition;
        }

        [DllImport("dwmapi.dll")]
        private static extern int DwmGetWindowAttribute(IntPtr hwnd, int dwAttribute, out RECT pvAttribute, int cbAttribute);

        [DllImport("user32.dll")]
        private static extern bool RedrawWindow(IntPtr hWnd, IntPtr lprcUpdate, IntPtr hrgnUpdate, uint flags);

        [DllImport("user32.dll")]
        private static extern bool UpdateWindow(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern int SetWindowLong(IntPtr hWnd, int nIndex, int dwNewLong);

        [DllImport("user32.dll")]
        private static extern int GetWindowLong(IntPtr hWnd, int nIndex);

        [DllImport("user32.dll")]
        private static extern bool GetWindowPlacement(IntPtr hWnd, ref WINDOWPLACEMENT lpwndpl);

        [DllImport("user32.dll")]
        private static extern bool IsWindow(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern int GetWindowTextLength(IntPtr hWnd);

        [DllImport("shell32.dll")]
        private static extern uint SHAppBarMessage(uint dwMessage, ref APPBARDATA pData);

        [DllImport("user32.dll")]
        private static extern IntPtr WindowFromPoint(Point Point);

        [DllImport("user32.dll")]
        private static extern IntPtr GetAncestor(IntPtr hWnd, uint gaFlags);

        [DllImport("user32.dll")]
        private static extern short GetAsyncKeyState(int vKey);

        [DllImport("user32.dll")]
        private static extern IntPtr SetWinEventHook(uint eventMin, uint eventMax, IntPtr hmodWinEventProc,
            WinEventDelegate lpfnWinEventProc, uint idProcess, uint idThread, uint dwFlags);

        [DllImport("user32.dll")]
        private static extern bool UnhookWinEvent(IntPtr hWinEventHook);

        [DllImport("user32.dll")]
        private static extern bool GetWindowRect(IntPtr hWnd, out RECT lpRect);

        [DllImport("user32.dll")]
        private static extern int GetSystemMetrics(int nIndex);

        [DllImport("user32.dll")]
        private static extern bool EnumWindows(EnumWindowsProc lpEnumFunc, IntPtr lParam);

        [DllImport("user32.dll")]
        private static extern bool IsIconic(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern bool GetCursorPos(out Point lpPoint);

        [DllImport("user32.dll")]
        private static extern IntPtr GetForegroundWindow();

        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern int GetClassName(IntPtr hWnd, StringBuilder lpClassName, int nMaxCount);

        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern int GetWindowText(IntPtr hWnd, StringBuilder lpString, int nMaxCount);

        [DllImport("user32.dll")]
        private static extern IntPtr SendMessage(IntPtr hWnd, uint Msg, IntPtr wParam, IntPtr lParam);

        [DllImport("user32.dll")]
        private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

        [DllImport("user32.dll")]
        private static extern int SystemParametersInfo(uint uiAction, uint uiParam, ref RECT pvParam, uint fWinIni);

        [DllImport("user32.dll", SetLastError = true, CharSet = CharSet.Auto)]
        private static extern IntPtr FindWindowEx(IntPtr hwndParent, IntPtr hwndChildAfter, string lpszClass, string lpszWindow);

        [DllImport("kernel32.dll")]
        private static extern bool CloseHandle(IntPtr hHandle);

        [DllImport("kernel32.dll")]
        private static extern bool SetThreadPriority(IntPtr hThread, int nPriority);

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool SetProcessPriorityBoost(IntPtr hProcess, bool bDisablePriorityBoost);

        [DllImport("kernel32.dll")]
        private static extern IntPtr OpenThread(uint dwDesiredAccess, bool bInheritHandle, uint dwThreadId);

        [DllImport("kernel32.dll")]
        private static extern bool SetThreadPriorityBoost(IntPtr hThread, bool bDisablePriorityBoost);

        [DllImport("user32.dll")]
        private static extern IntPtr FindWindow(string lpClassName, string lpWindowName);

        [DllImport("user32.dll")]
        private static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);

        [DllImport("user32.dll")]
        private static extern bool IsWindowVisible(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern bool GetLastInputInfo(ref LASTINPUTINFO plii);

        [DllImport("user32.dll")]
        private static extern int ShowCursor(bool bShow);

        [DllImport("user32.dll")]
        private static extern bool SetCursorPos(int x, int y);

        [DllImport("user32.dll")]
        private static extern bool ClipCursor(ref RECT lpRect);

        [DllImport("user32.dll")]
        private static extern bool ClipCursor(IntPtr lpRect);

        [DllImport("user32.dll")]
        private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

        [DllImport("user32.dll")]
        private static extern bool EnumDisplaySettings(string deviceName, int modeNum, ref DEVMODE devMode);

        [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Ansi)]
        private struct DEVMODE
        {
            private const int CCHDEVICENAME = 32;
            private const int CCHFORMNAME = 32;

            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = CCHDEVICENAME)]
            public string dmDeviceName;
            public ushort dmSpecVersion;
            public ushort dmDriverVersion;
            public ushort dmSize;
            public ushort dmDriverExtra;
            public uint dmFields;

            public int dmPositionX;
            public int dmPositionY;
            public uint dmDisplayOrientation;
            public uint dmDisplayFixedOutput;

            public short dmColor;
            public short dmDuplex;
            public short dmYResolution;
            public short dmTTOption;
            public short dmCollate;

            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = CCHFORMNAME)]
            public string dmFormName;
            public ushort dmLogPixels;
            public uint dmBitsPerPel;
            public uint dmPelsWidth;
            public uint dmPelsHeight;
            public uint dmDisplayFlags;
            public uint dmDisplayFrequency;

            public uint dmICMMethod;
            public uint dmICMIntent;
            public uint dmMediaType;
            public uint dmDitherType;
            public uint dmReserved1;
            public uint dmReserved2;

            public uint dmPanningWidth;
            public uint dmPanningHeight;
        }

        [STAThread]
        static void Main()
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            InitializeMonitorSettings();
            LoadSettings();
            if (_desktopIconsHidingEnabled)
            {
                StartDesktopMonitoring();
            }
            MagicTrick();
            SetupTrayIcon();
            SetupOverlayWindows();
            StartInactivityTimer();
            StartEdgeTimer();

            Application.Run();
        }

        static void MagicTrick()
        {
            var currentProcess = Process.GetCurrentProcess();
            try
            {
                currentProcess.PriorityClass = ProcessPriorityClass.Idle;
                SetProcessPriorityBoost(currentProcess.Handle, true);
            }
            catch
            {
            }

            foreach (ProcessThread thread in currentProcess.Threads)
            {
                try
                {
                    uint access = THREAD_SET_INFORMATION | THREAD_QUERY_INFORMATION;
                    IntPtr hThread = OpenThread(access, false, (uint)thread.Id);
                    if (hThread != IntPtr.Zero)
                    {
                        SetThreadPriority(hThread, THREAD_PRIORITY_IDLE);
                        SetThreadPriorityBoost(hThread, true);
                        CloseHandle(hThread);
                    }
                }
                catch
                {
                }
            }
        }

        private static void StartEdgeTimer()
        {
            _edgeTimer = new Timer { Interval = 100 };
            _edgeTimer.Tick += (s, e) =>
            {
                if (!_taskbarHidingEnabled) return;

                if (IsWindowsKeyPressed())
                {
                    _lastWindowsKeyTime = DateTime.Now;
                    ShowTaskbarAndDesktop();
                    _lastTaskbarInteractionTime = DateTime.Now;
                    return;
                }

                if ((DateTime.Now - _lastWindowsKeyTime) < _winKeyShowDuration)
                {
                    ShowTaskbarAndDesktop();
                    _lastTaskbarInteractionTime = DateTime.Now;
                    return;
                }

                var pos = Cursor.Position;
                var bottom = Screen.PrimaryScreen.Bounds.Bottom;
                bool nearEdge = pos.Y >= bottom - _activityThreshold;

                if (nearEdge)
                {
                    ShowTaskbarAndDesktop();
                    _lastTaskbarInteractionTime = DateTime.Now;
                }
                else
                {
                    if (!_taskbarHidden)
                    {
                        if (_lastTaskbarInteractionTime == DateTime.MinValue)
                        {
                            _lastTaskbarInteractionTime = DateTime.Now;
                        }

                        var elapsed = DateTime.Now - _lastTaskbarInteractionTime;
                        if (elapsed.TotalSeconds >= _taskbarTimeoutSeconds)
                        {
                            HideTaskbarAndDesktop();
                            _lastTaskbarInteractionTime = DateTime.MinValue;
                        }
                    }
                }
            };
            _edgeTimer.Start();
        }

        private static void InitializeMonitorSettings()
        {
            foreach (var screen in Screen.AllScreens)
            {
                var displayName = $"Monitor {Array.IndexOf(Screen.AllScreens, screen) + 1}";
                if (screen == Screen.PrimaryScreen)
                    displayName += " (Primary)";

                _monitorSettings[screen.DeviceName] = new MonitorSettings
                {
                    DeviceName = screen.DeviceName,
                    DisplayName = displayName,
                    Enabled = true,
                    TimeoutSeconds = 25
                };
            }
        }

        private static void ShowOverlayOpacityDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Overlay Opacity Settings";
                form.Size = new Size(350, 200);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var opacityLabel = new Label
                {
                    Text = "Normal Opacity (0.1 - 1.0):",
                    Location = new Point(20, 20),
                    Size = new Size(150, 20)
                };

                var opacityTextBox = new TextBox
                {
                    Text = _overlayOpacity.ToString("F1"),
                    Location = new Point(180, 20),
                    Size = new Size(100, 20)
                };

                var fadedOpacityLabel = new Label
                {
                    Text = "Faded Opacity (0.1 - 1.0):",
                    Location = new Point(20, 60),
                    Size = new Size(150, 20)
                };

                var fadedOpacityTextBox = new TextBox
                {
                    Text = _overlayFadedOpacity.ToString("F1"),
                    Location = new Point(180, 60),
                    Size = new Size(100, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(120, 120),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                var cancelButton = new Button
                {
                    Text = "Cancel",
                    Location = new Point(200, 120),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.Cancel
                };

                form.Controls.AddRange(new Control[]
                {
                    opacityLabel, opacityTextBox, fadedOpacityLabel, fadedOpacityTextBox, okButton, cancelButton
                });
                form.AcceptButton = okButton;
                form.CancelButton = cancelButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (double.TryParse(opacityTextBox.Text, out double opacity) && opacity >= 0.1 && opacity <= 1.0)
                    {
                        _overlayOpacity = opacity;
                    }

                    if (double.TryParse(fadedOpacityTextBox.Text, out double fadedOpacity) && fadedOpacity >= 0.1 && fadedOpacity <= 1.0)
                    {
                        _overlayFadedOpacity = fadedOpacity;
                    }

                    SaveSettings();
                }
            }
        }

        private static void ShowActivityThresholdDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Taskbar Threshold Settings";
                form.Size = new Size(355, 195);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Taskbar Threshold (mouse movement distance):",
                    Location = new Point(20, 20),
                    Size = new Size(280, 20)
                };

                var numericUpDown = new NumericUpDown
                {
                    Location = new Point(20, 50),
                    Size = new Size(100, 23),
                    Minimum = 10,
                    Maximum = 1000,
                    Value = _activityThreshold
                };

                var descLabel = new Label
                {
                    Text = "Distance from bottom edge of screen to trigger taskbar\nLower values = closer to edge, Higher values = further from edge",
                    Location = new Point(20, 80),
                    Size = new Size(280, 40),
                    ForeColor = Color.Gray
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(180, 130),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                var cancelButton = new Button
                {
                    Text = "Cancel",
                    Location = new Point(260, 130),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.Cancel
                };

                form.Controls.AddRange(new Control[] { label, numericUpDown, descLabel, okButton, cancelButton });
                form.AcceptButton = okButton;
                form.CancelButton = cancelButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    _activityThreshold = (int)numericUpDown.Value;
                    SaveSettings();
                }
            }
        }

        private static void ShowTimeoutDialog(MonitorSettings setting)
        {
            using (var form = new Form())
            {
                form.Text = $"Overlay Timeout Settings - {setting.DisplayName}";
                form.Size = new Size(300, 150);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Overlay Timeout (seconds):",
                    Location = new Point(20, 20),
                    Size = new Size(140, 20)
                };

                var textBox = new TextBox
                {
                    Text = setting.TimeoutSeconds.ToString(),
                    Location = new Point(170, 18),
                    Size = new Size(100, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(120, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                var cancelButton = new Button
                {
                    Text = "Cancel",
                    Location = new Point(200, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.Cancel
                };

                form.Controls.AddRange(new Control[] { label, textBox, okButton, cancelButton });
                form.AcceptButton = okButton;
                form.CancelButton = cancelButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (int.TryParse(textBox.Text, out int timeout) && timeout > 0)
                    {
                        setting.TimeoutSeconds = timeout;
                        SaveSettings();
                    }
                    else
                    {
                        MessageBox.Show("Please enter a valid timeout value (positive integer).", "Invalid Input",
                            MessageBoxButtons.OK, MessageBoxIcon.Warning);
                    }
                }
            }
        }

        private static void ShowTaskbarTimeoutDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Taskbar Timeout Settings";
                form.Size = new Size(300, 150);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Taskbar Timeout (seconds):",
                    Location = new Point(20, 20),
                    Size = new Size(160, 20)
                };

                var textBox = new TextBox
                {
                    Text = _taskbarTimeoutSeconds.ToString(),
                    Location = new Point(190, 18),
                    Size = new Size(70, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(120, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                form.Controls.AddRange(new Control[] { label, textBox, okButton });
                form.AcceptButton = okButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (int.TryParse(textBox.Text, out int timeout) && timeout > 0)
                    {
                        _taskbarTimeoutSeconds = timeout;
                        SaveSettings();
                    }
                    else
                    {
                        MessageBox.Show("Please enter a valid timeout value (positive integer).", "Invalid Input",
                            MessageBoxButtons.OK, MessageBoxIcon.Warning);
                    }
                }
            }
        }

        private static void ShowOverlayTimeoutDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Draw Black Overlay Timeout Settings";
                form.Size = new Size(300, 150);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Draw Black Overlay Timeout (seconds):",
                    Location = new Point(20, 20),
                    Size = new Size(200, 20)
                };

                var textBox = new TextBox
                {
                    Text = _drawBlackOverlayEnabledTimeoutSeconds.ToString(),
                    Location = new Point(220, 18),
                    Size = new Size(50, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(100, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                form.Controls.AddRange(new Control[] { label, textBox, okButton });
                form.AcceptButton = okButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (int.TryParse(textBox.Text, out int timeout) && timeout > 0)
                    {
                        _drawBlackOverlayEnabledTimeoutSeconds = timeout;
                        SaveSettings();
                    }
                    else
                    {
                        MessageBox.Show("Please enter a valid timeout value (positive integer).", "Invalid Input",
                            MessageBoxButtons.OK, MessageBoxIcon.Warning);
                    }
                }
            }
        }

        private static void ShowDisplayOffTimeoutDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Display Off Timeout Settings";
                form.Size = new Size(300, 150);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Display Off Timeout (seconds):",
                    Location = new Point(20, 20),
                    Size = new Size(180, 20)
                };

                var textBox = new TextBox
                {
                    Text = _displayOffTimeoutSeconds.ToString(),
                    Location = new Point(200, 18),
                    Size = new Size(70, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(120, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                form.Controls.AddRange(new Control[] { label, textBox, okButton });
                form.AcceptButton = okButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (int.TryParse(textBox.Text, out int timeout) && timeout > 0)
                        _displayOffTimeoutSeconds = timeout;
                    else
                        MessageBox.Show("Enter a valid timeout (positive integer).", "Invalid Input", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                }
            }
        }

        private static void ShowDesktopIconsTimeoutDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Desktop Icons Timeout Settings";
                form.Size = new Size(300, 150);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var label = new Label
                {
                    Text = "Desktop Icons Timeout (seconds):",
                    Location = new Point(20, 20),
                    Size = new Size(200, 20)
                };

                var textBox = new TextBox
                {
                    Text = _desktopIconsTimeoutSeconds.ToString(),
                    Location = new Point(220, 18),
                    Size = new Size(50, 20)
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(100, 60),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                form.Controls.AddRange(new Control[] { label, textBox, okButton });
                form.AcceptButton = okButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    if (int.TryParse(textBox.Text, out int timeout) && timeout > 0)
                    {
                        _desktopIconsTimeoutSeconds = timeout;
                        SaveSettings();
                    }
                    else
                    {
                        MessageBox.Show("Please enter a valid timeout value (positive integer).", "Invalid Input",
                            MessageBoxButtons.OK, MessageBoxIcon.Warning);
                    }
                }
            }
        }

        private static List<string> GetAllActiveProcessNamesWithWindows()
        {
            var processesWithWindows = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

            EnumWindows((hWnd, lParam) =>
            {
                if (IsWindowVisible(hWnd))
                {
                    uint pid;
                    GetWindowThreadProcessId(hWnd, out pid);

                    try
                    {
                        var proc = Process.GetProcessById((int)pid);
                        if (!string.IsNullOrEmpty(proc.ProcessName))
                            processesWithWindows.Add(proc.ProcessName);
                    }
                    catch
                    {
                    }
                }
                return true;
            }, IntPtr.Zero);

            return processesWithWindows.ToList();
        }

        private static void ShowExclusionsDialog()
        {
            using (var form = new Form())
            {
                form.Text = "Manage Excluded Processes";
                form.Size = new Size(520, 520);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;
                form.BackColor = Color.FromArgb(32, 32, 32);
                form.ForeColor = Color.White;

                const int margin = 20;
                const int spacing = 10;
                const int buttonHeight = 30;
                const int textBoxHeight = 23;
                const int listBoxWidth = 200;
                const int listBoxHeight = 280;

                var excludedLabel = new Label
                {
                    Text = "Excluded Processes:",
                    Location = new Point(margin, margin),
                    Size = new Size(listBoxWidth, 20),
                    Font = new Font("Segoe UI", 9F, FontStyle.Bold),
                    ForeColor = Color.White,
                    BackColor = Color.FromArgb(32, 32, 32)
                };

                var activeLabel = new Label
                {
                    Text = "Active Processes:",
                    Location = new Point(margin * 2 + listBoxWidth + spacing, margin),
                    Size = new Size(listBoxWidth, 20),
                    Font = new Font("Segoe UI", 9F, FontStyle.Bold),
                    ForeColor = Color.White,
                    BackColor = Color.FromArgb(32, 32, 32)
                };

                var excludedListBox = new ListBox
                {
                    Location = new Point(margin, margin + 25),
                    Size = new Size(listBoxWidth, listBoxHeight),
                    SelectionMode = SelectionMode.One,
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(24, 24, 24),
                    ForeColor = Color.White,
                    BorderStyle = BorderStyle.FixedSingle
                };

                foreach (var excluded in _excludedWindowTitles)
                {
                    excludedListBox.Items.Add(excluded);
                }

                var activeProcessesListBox = new ListBox
                {
                    Location = new Point(margin * 2 + listBoxWidth + spacing, margin + 25),
                    Size = new Size(listBoxWidth, listBoxHeight),
                    SelectionMode = SelectionMode.One,
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(24, 24, 24),
                    ForeColor = Color.White,
                    BorderStyle = BorderStyle.FixedSingle
                };

                int buttonsY = margin + 25 + listBoxHeight + spacing;

                var addButton = new Button
                {
                    Text = "Add",
                    Location = new Point(margin * 2 + listBoxWidth + spacing, buttonsY),
                    Size = new Size(80, buttonHeight),
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(45, 45, 45),
                    ForeColor = Color.White,
                    FlatStyle = FlatStyle.Flat
                };
                addButton.FlatAppearance.BorderColor = Color.FromArgb(70, 70, 70);

                var removeButton = new Button
                {
                    Text = "Remove",
                    Location = new Point(margin, buttonsY),
                    Size = new Size(80, buttonHeight),
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(45, 45, 45),
                    ForeColor = Color.White,
                    FlatStyle = FlatStyle.Flat
                };
                removeButton.FlatAppearance.BorderColor = Color.FromArgb(70, 70, 70);

                int manualY = buttonsY + buttonHeight + spacing;

                var manualLabel = new Label
                {
                    Text = "Manual add:",
                    Location = new Point(margin, manualY),
                    Size = new Size(80, 20),
                    Font = new Font("Segoe UI", 9F),
                    ForeColor = Color.White,
                    BackColor = Color.FromArgb(32, 32, 32)
                };

                var manualInput = new TextBox
                {
                    Location = new Point(margin, manualY + 25),
                    Size = new Size(listBoxWidth - 80, textBoxHeight),
                    PlaceholderText = "Process name...",
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(24, 24, 24),
                    ForeColor = Color.White,
                    BorderStyle = BorderStyle.FixedSingle
                };

                var addManualButton = new Button
                {
                    Text = "Add",
                    Location = new Point(margin + listBoxWidth - 75, manualY + 25),
                    Size = new Size(75, buttonHeight),
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(45, 45, 45),
                    ForeColor = Color.White,
                    FlatStyle = FlatStyle.Flat
                };
                addManualButton.FlatAppearance.BorderColor = Color.FromArgb(70, 70, 70);

                int bottomY = form.ClientSize.Height - buttonHeight - margin;

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(form.ClientSize.Width - 160, bottomY),
                    Size = new Size(75, buttonHeight),
                    DialogResult = DialogResult.OK,
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(45, 45, 45),
                    ForeColor = Color.White,
                    FlatStyle = FlatStyle.Flat
                };
                okButton.FlatAppearance.BorderColor = Color.FromArgb(70, 70, 70);

                var cancelButton = new Button
                {
                    Text = "Cancel",
                    Location = new Point(form.ClientSize.Width - 80, bottomY),
                    Size = new Size(75, buttonHeight),
                    DialogResult = DialogResult.Cancel,
                    Font = new Font("Segoe UI", 9F),
                    BackColor = Color.FromArgb(45, 45, 45),
                    ForeColor = Color.White,
                    FlatStyle = FlatStyle.Flat
                };
                cancelButton.FlatAppearance.BorderColor = Color.FromArgb(70, 70, 70);

                addButton.Click += (s, e) =>
                {
                    if (activeProcessesListBox.SelectedItem != null)
                    {
                        var selectedProcess = activeProcessesListBox.SelectedItem.ToString();
                        if (!excludedListBox.Items.Contains(selectedProcess))
                        {
                            excludedListBox.Items.Add(selectedProcess);
                        }
                    }
                };

                removeButton.Click += (s, e) =>
                {
                    if (excludedListBox.SelectedItem != null)
                    {
                        excludedListBox.Items.Remove(excludedListBox.SelectedItem);
                    }
                };

                addManualButton.Click += (s, e) =>
                {
                    if (!string.IsNullOrWhiteSpace(manualInput.Text))
                    {
                        var processName = manualInput.Text.Trim();
                        if (!excludedListBox.Items.Contains(processName))
                        {
                            excludedListBox.Items.Add(processName);
                            manualInput.Clear();
                        }
                    }
                };

                manualInput.KeyDown += (s, e) =>
                {
                    if (e.KeyCode == Keys.Enter)
                    {
                        addManualButton.PerformClick();
                        e.Handled = true;
                        e.SuppressKeyPress = true;
                    }
                };

                void UpdateActiveProcesses()
                {
                    try
                    {
                        var activeProcesses = GetAllActiveProcessNamesWithWindows();
                        var currentItems = activeProcessesListBox.Items.Cast<string>().ToHashSet();
                        var newItems = new HashSet<string>(activeProcesses);

                        if (!currentItems.SetEquals(newItems))
                        {
                            var selectedItem = activeProcessesListBox.SelectedItem?.ToString();
                            activeProcessesListBox.Items.Clear();

                            foreach (var process in activeProcesses.OrderBy(p => p))
                            {
                                activeProcessesListBox.Items.Add(process);
                            }

                            if (selectedItem != null && activeProcessesListBox.Items.Contains(selectedItem))
                            {
                                activeProcessesListBox.SelectedItem = selectedItem;
                            }
                        }
                    }
                    catch
                    {
                    }
                }

                var updateTimer = new Timer { Interval = 1000 };
                updateTimer.Tick += (s, e) => UpdateActiveProcesses();
                updateTimer.Start();

                UpdateActiveProcesses();

                form.Controls.AddRange(new Control[]
                {
                    excludedLabel,
                    activeLabel,
                    excludedListBox,
                    activeProcessesListBox,
                    addButton,
                    removeButton,
                    manualLabel,
                    manualInput,
                    addManualButton,
                    okButton,
                    cancelButton
                });

                form.AcceptButton = okButton;
                form.CancelButton = cancelButton;

                var result = form.ShowDialog();
                updateTimer.Stop();
                updateTimer.Dispose();

                if (result == DialogResult.OK)
                {
                    _excludedWindowTitles.Clear();
                    foreach (var item in excludedListBox.Items)
                    {
                        _excludedWindowTitles.Add(item.ToString());
                    }
                    SaveSettings();
                }
            }
        }

        private static readonly string SettingsFilePath = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
            "OLEDSaver",
            "settings.json"
        );

        public class AppSettings
        {
            public Dictionary<string, MonitorSettings> MonitorSettings { get; set; } = new();

            public int TaskbarThreshold { get; set; } = 150;
            public bool TaskbarHidingEnabled { get; set; }
            public bool DesktopIconsHidingEnabled { get; set; }
            public bool DrawBlackOverlayEnabled { get; set; }
            public bool ScreenOffEnabled { get; set; }
            public int TaskbarTimeoutSeconds { get; set; }
            public int DesktopIconsTimeoutSeconds { get; set; }
            public int OverlayWindowsTimeoutSeconds { get; set; }
            public int DisplayOffTimeoutSeconds { get; set; }
            public List<string> ExcludedWindowTitles { get; set; } = new List<string>();
            public bool OverlayRoundedCorners { get; set; } = true;
            public double OverlayOpacity { get; set; } = 0.93;
            public double OverlayFadedOpacity { get; set; } = 0.6;
        }

        private static void SaveSettings()
        {
            try
            {
                var settings = new AppSettings
                {
                    TaskbarThreshold = _activityThreshold,
                    TaskbarHidingEnabled = _taskbarHidingEnabled,
                    DesktopIconsHidingEnabled = _desktopIconsHidingEnabled,
                    DrawBlackOverlayEnabled = _drawBlackOverlayEnabled,
                    ScreenOffEnabled = _screenOffEnabled,
                    TaskbarTimeoutSeconds = _taskbarTimeoutSeconds,
                    DesktopIconsTimeoutSeconds = _desktopIconsTimeoutSeconds,
                    OverlayWindowsTimeoutSeconds = _drawBlackOverlayEnabledTimeoutSeconds,
                    DisplayOffTimeoutSeconds = _displayOffTimeoutSeconds,
                    MonitorSettings = _monitorSettings,
                    ExcludedWindowTitles = _excludedWindowTitles.ToList(),
                    OverlayRoundedCorners = _overlayRoundedCorners,
                    OverlayOpacity = _overlayOpacity,
                    OverlayFadedOpacity = _overlayFadedOpacity
                };

                var directory = Path.GetDirectoryName(SettingsFilePath);
                if (!Directory.Exists(directory))
                {
                    Directory.CreateDirectory(directory);
                }

                var json = JsonSerializer.Serialize(settings, new JsonSerializerOptions
                {
                    WriteIndented = true
                });

                File.WriteAllText(SettingsFilePath, json);
            }
            catch
            {
            }
        }

        private static void LoadSettings()
        {
            try
            {
                if (!File.Exists(SettingsFilePath))
                    return;

                var json = File.ReadAllText(SettingsFilePath);
                var settings = JsonSerializer.Deserialize<AppSettings>(json);

                if (settings != null)
                {
                    _taskbarHidingEnabled = settings.TaskbarHidingEnabled;
                    _desktopIconsHidingEnabled = settings.DesktopIconsHidingEnabled;
                    _drawBlackOverlayEnabled = settings.DrawBlackOverlayEnabled;
                    _screenOffEnabled = settings.ScreenOffEnabled;
                    _taskbarTimeoutSeconds = settings.TaskbarTimeoutSeconds;
                    _desktopIconsTimeoutSeconds = settings.DesktopIconsTimeoutSeconds;
                    _drawBlackOverlayEnabledTimeoutSeconds = settings.OverlayWindowsTimeoutSeconds;
                    _displayOffTimeoutSeconds = settings.DisplayOffTimeoutSeconds;
                    _activityThreshold = settings.TaskbarThreshold;
                    _overlayRoundedCorners = settings.OverlayRoundedCorners;
                    _overlayOpacity = settings.OverlayOpacity;
                    _overlayFadedOpacity = settings.OverlayFadedOpacity;

                    if (settings.ExcludedWindowTitles != null)
                        _excludedWindowTitles = settings.ExcludedWindowTitles.ToList();

                    if (settings.MonitorSettings != null)
                    {
                        foreach (var kvp in settings.MonitorSettings)
                        {
                            if (_monitorSettings.ContainsKey(kvp.Key))
                            {
                                _monitorSettings[kvp.Key].Enabled = kvp.Value.Enabled;
                                _monitorSettings[kvp.Key].TimeoutSeconds = kvp.Value.TimeoutSeconds;
                            }
                        }
                    }
                }
            }
            catch
            {
            }
        }

        private static void SetupTrayIcon()
        {
            _contextMenu = new ContextMenuStrip();
            _contextMenu.RenderMode = ToolStripRenderMode.Professional;
            _contextMenu.Renderer = new DarkRenderer();
            _contextMenu.BackColor = Color.FromArgb(32, 32, 32);
            _contextMenu.ForeColor = Color.White;

            Icon icon;
            try
            {
                icon = LoadTrayIconFromResources();
            }
            catch
            {
                try
                {
                    icon = new Icon("app.ico");
                }
                catch
                {
                    icon = SystemIcons.Application;
                }
            }

            _trayIcon = new NotifyIcon
            {
                Text = "OLED Saver",
                Visible = true,
                Icon = icon
            };

            var enabledFeaturesMenuItem = new ToolStripMenuItem("Enabled Features")
            {
                ForeColor = Color.White
            };

            var taskbarHidingItem = new ToolStripMenuItem("Hide Taskbar")
            {
                Checked = _taskbarHidingEnabled,
                CheckOnClick = true,
                ForeColor = Color.White
            };
            taskbarHidingItem.Click += (s, e) =>
            {
                _taskbarHidingEnabled = taskbarHidingItem.Checked;

                if (!_taskbarHidingEnabled)
                {
                    ShowTaskbarAndDesktop();
                }

                SaveSettings();
            };

            var desktopIconsHidingItem = new ToolStripMenuItem("Hide Desktop Icons")
            {
                Checked = _desktopIconsHidingEnabled,
                CheckOnClick = true,
                ForeColor = Color.White
            };
            desktopIconsHidingItem.Click += (s, e) =>
            {
                _desktopIconsHidingEnabled = desktopIconsHidingItem.Checked;

                if (_desktopIconsHidingEnabled)
                {
                    StartDesktopMonitoring();
                }
                else
                {
                    StopDesktopMonitoring();
                    ShowDesktopIconsIfNeeded();
                }
                SaveSettings();
            };

            var drawBlackOverlay = new ToolStripMenuItem("Draw Black Overlay")
            {
                Checked = _drawBlackOverlayEnabled,
                CheckOnClick = true,
                ForeColor = Color.White
            };
            drawBlackOverlay.Click += (s, e) =>
            {
                _drawBlackOverlayEnabled = drawBlackOverlay.Checked;
                if (!_drawBlackOverlayEnabled)
                {
                    _overlayUpdateCts?.Cancel();
                    _drawBlackOverlay = false;
                    HideBlackOverlays();
                    _windowThatTriggeredOverlay = IntPtr.Zero;
                    _overlayFaded = false;
                }
                SaveSettings();
            };

            var screenOffItem = new ToolStripMenuItem("Turn Off Display")
            {
                Checked = _screenOffEnabled,
                CheckOnClick = true,
                ForeColor = Color.White
            };
            screenOffItem.Click += (s, e) =>
            {
                _screenOffEnabled = screenOffItem.Checked;
                if (!_screenOffEnabled && _screenOff)
                {
                    TurnOnDisplay();
                }
                SaveSettings();
            };

            enabledFeaturesMenuItem.DropDownItems.AddRange(new ToolStripItem[]
            {
                taskbarHidingItem, desktopIconsHidingItem, drawBlackOverlay, screenOffItem
            });

            _contextMenu.Items.Add(enabledFeaturesMenuItem);
            _contextMenu.Items.Add(new ToolStripSeparator());

            var timeoutMenuItem = new ToolStripMenuItem("Timeout Settings")
            {
                ForeColor = Color.White
            };

            var taskbarTimeoutItem = new ToolStripMenuItem("Taskbar Timeout...")
            {
                ForeColor = Color.White
            };
            taskbarTimeoutItem.Click += (s, e) => ShowTaskbarTimeoutDialog();
            timeoutMenuItem.DropDownItems.Add(taskbarTimeoutItem);

            var desktopIconsTimeoutItem = new ToolStripMenuItem("Desktop Icons Timeout...")
            {
                ForeColor = Color.White
            };
            desktopIconsTimeoutItem.Click += (s, e) => ShowDesktopIconsTimeoutDialog();
            timeoutMenuItem.DropDownItems.Add(desktopIconsTimeoutItem);

            var drawBlackOverlayTimeoutItem = new ToolStripMenuItem("Draw Black Overlay Windows Timeout...")
            {
                ForeColor = Color.White
            };
            drawBlackOverlayTimeoutItem.Click += (s, e) => ShowOverlayTimeoutDialog();
            timeoutMenuItem.DropDownItems.Add(drawBlackOverlayTimeoutItem);

            var displayOffTimeoutItem = new ToolStripMenuItem("Display Off Timeout...")
            {
                ForeColor = Color.White
            };
            displayOffTimeoutItem.Click += (s, e) => ShowDisplayOffTimeoutDialog();
            timeoutMenuItem.DropDownItems.Add(displayOffTimeoutItem);

            var activityThresholdItem = new ToolStripMenuItem("Taskbar Threshold...")
            {
                ForeColor = Color.White
            };
            activityThresholdItem.Click += (s, e) => ShowActivityThresholdDialog();
            timeoutMenuItem.DropDownItems.Add(activityThresholdItem);

            _contextMenu.Items.Add(timeoutMenuItem);

            var overlaySettingsMenuItem = new ToolStripMenuItem("Overlay Settings")
            {
                ForeColor = Color.White
            };

            var roundedCornersItem = new ToolStripMenuItem("Rounded Corners")
            {
                Checked = _overlayRoundedCorners,
                CheckOnClick = true,
                ForeColor = Color.White
            };
            roundedCornersItem.Click += (s, e) =>
            {
                _overlayRoundedCorners = roundedCornersItem.Checked;
                SaveSettings();
            };

            var opacitySettingsItem = new ToolStripMenuItem("Opacity Settings...")
            {
                ForeColor = Color.White
            };
            opacitySettingsItem.Click += (s, e) => ShowOverlayOpacityDialog();

            overlaySettingsMenuItem.DropDownItems.AddRange(new ToolStripItem[]
            {
                roundedCornersItem, opacitySettingsItem
            });

            _contextMenu.Items.Add(overlaySettingsMenuItem);

            var monitorsMenuItem = new ToolStripMenuItem("Monitor Settings")
            {
                ForeColor = Color.White
            };
            foreach (var setting in _monitorSettings.Values)
            {
                var monitorItem = new ToolStripMenuItem(setting.DisplayName)
                {
                    ForeColor = Color.White
                };

                var enabledItem = new ToolStripMenuItem("Enabled")
                {
                    Checked = setting.Enabled,
                    CheckOnClick = true,
                    Tag = setting,
                    ForeColor = Color.White
                };
                enabledItem.Click += (s, e) =>
                {
                    var menuItem = s as ToolStripMenuItem;
                    var monitorSetting = menuItem.Tag as MonitorSettings;
                    monitorSetting.Enabled = menuItem.Checked;
                    SaveSettings();
                };

                var overlayTimeoutItem = new ToolStripMenuItem("Overlay Timeout...")
                {
                    ForeColor = Color.White
                };
                overlayTimeoutItem.Click += (s, e) => ShowTimeoutDialog(setting);

                monitorItem.DropDownItems.Add(enabledItem);
                monitorItem.DropDownItems.Add(overlayTimeoutItem);
                monitorsMenuItem.DropDownItems.Add(monitorItem);
            }

            _contextMenu.Items.Add(monitorsMenuItem);

            var exclusionsItem = new ToolStripMenuItem("Manage Exclusions...")
            {
                ForeColor = Color.White
            };

            _contextMenu.Items.Add(new ToolStripSeparator());

            exclusionsItem.Click += (s, e) => ShowExclusionsDialog();
            _contextMenu.Items.Add(exclusionsItem);

            _contextMenu.Items.Add(new ToolStripSeparator());

            var telegramItem = new ToolStripMenuItem("Telegram Channel")
            {
                ForeColor = Color.White
            };
            telegramItem.Click += (s, e) =>
            {
                try
                {
                    var psi = new ProcessStartInfo("https://t.me/arsenzaa")
                    {
                        UseShellExecute = true
                    };
                    Process.Start(psi);
                }
                catch
                {
                }
            };

            _contextMenu.Items.Add(telegramItem);

            var autoStartItem = new ToolStripMenuItem("Start with Windows")
            {
                Checked = IsAutoStartEnabled(),
                CheckOnClick = true,
                ForeColor = Color.White
            };

            autoStartItem.Click += (s, e) =>
            {
                EnableAutoStart(autoStartItem.Checked);
            };

            _contextMenu.Items.Add(autoStartItem);

            var exitItem = new ToolStripMenuItem("Exit")
            {
                ForeColor = Color.White
            };
            exitItem.Click += (s, e) => ExitApplication();
            _contextMenu.Items.Add(exitItem);

            _trayIcon.ContextMenuStrip = _contextMenu;
            _trayIcon.DoubleClick += (s, e) => ShowSettingsDialog();

            if (_taskbarHidingEnabled)
                HideTaskbarAndDesktop();
        }

        private static void ShowSettingsDialog()
        {
            using (var form = new Form())
            {
                form.Text = "OLED Saver Settings";
                form.Size = new Size(420, 300);
                form.StartPosition = FormStartPosition.CenterScreen;
                form.FormBorderStyle = FormBorderStyle.FixedDialog;
                form.MaximizeBox = false;
                form.MinimizeBox = false;

                var listView = new ListView
                {
                    Location = new Point(20, 20),
                    Size = new Size(370, 180),
                    View = View.Details,
                    FullRowSelect = true,
                    GridLines = true,
                    CheckBoxes = true
                };

                listView.Columns.Add("Monitor", 200);
                listView.Columns.Add("Overlay Timeout", 100);
                listView.Columns.Add("Status", 80);

                foreach (var setting in _monitorSettings.Values)
                {
                    var item = new ListViewItem(setting.DisplayName)
                    {
                        Checked = setting.Enabled,
                        Tag = setting
                    };
                    item.SubItems.Add(setting.TimeoutSeconds.ToString() + "s");
                    item.SubItems.Add(setting.Enabled ? "Enabled" : "Disabled");
                    listView.Items.Add(item);
                }

                var editOverlayButton = new Button
                {
                    Text = "Edit Overlay",
                    Location = new Point(20, 220),
                    Size = new Size(100, 23)
                };
                editOverlayButton.Click += (s, e) =>
                {
                    if (listView.SelectedItems.Count > 0)
                    {
                        var setting = listView.SelectedItems[0].Tag as MonitorSettings;
                        ShowTimeoutDialog(setting);
                        listView.SelectedItems[0].SubItems[1].Text = setting.TimeoutSeconds.ToString() + "s";
                    }
                };

                var okButton = new Button
                {
                    Text = "OK",
                    Location = new Point(240, 220),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.OK
                };

                var cancelButton = new Button
                {
                    Text = "Cancel",
                    Location = new Point(320, 220),
                    Size = new Size(75, 23),
                    DialogResult = DialogResult.Cancel
                };

                form.Controls.AddRange(new Control[] { listView, editOverlayButton, okButton, cancelButton });
                form.AcceptButton = okButton;
                form.CancelButton = cancelButton;

                if (form.ShowDialog() == DialogResult.OK)
                {
                    foreach (ListViewItem item in listView.Items)
                    {
                        var setting = item.Tag as MonitorSettings;
                        setting.Enabled = item.Checked;
                    }
                    SaveSettings();
                }
            }
        }

        public static void EnableAutoStart(bool enable)
        {
            try
            {
                if (enable)
                {
                    CreateShortcut();
                }
                else
                {
                    RemoveShortcut();
                }
            }
            catch
            {
            }
        }

        private static Icon LoadTrayIconFromResources()
        {
            var assembly = Assembly.GetExecutingAssembly();
            using Stream stream = assembly.GetManifestResourceStream(TrayIconResourceName);
            if (stream == null)
            {
                throw new InvalidOperationException($"Resource '{TrayIconResourceName}' was not found.");
            }

            return new Icon(stream);
        }

        private static void CreateShortcut()
        {
            try
            {
                Type shellType = Type.GetTypeFromProgID("WScript.Shell");
                if (shellType == null) return;
                object shell = Activator.CreateInstance(shellType);
                object shortcut = shellType.InvokeMember("CreateShortcut", BindingFlags.InvokeMethod, null, shell, new object[] { ShortcutPath });
                Type shortcutType = shortcut.GetType();
                shortcutType.InvokeMember("Description", BindingFlags.SetProperty, null, shortcut, new object[] { "OLEDSaver Auto Start" });
                shortcutType.InvokeMember("TargetPath", BindingFlags.SetProperty, null, shortcut, new object[] { Application.ExecutablePath });
                shortcutType.InvokeMember("WorkingDirectory", BindingFlags.SetProperty, null, shortcut, new object[] { Path.GetDirectoryName(Application.ExecutablePath) });
                shortcutType.InvokeMember("Save", BindingFlags.InvokeMethod, null, shortcut, null);
            }
            catch
            {
            }
        }

        private static void RemoveShortcut()
        {
            if (File.Exists(ShortcutPath))
            {
                File.Delete(ShortcutPath);
            }
        }

        public static bool IsAutoStartEnabled()
        {
            return File.Exists(ShortcutPath);
        }

        public static string GetStartupFolder()
        {
            return StartupFolderPath;
        }

        private const int VK_LWIN = 0x5B;
        private const int VK_RWIN = 0x5C;

        private static bool IsWindowsKeyPressed()
        {
            return (GetAsyncKeyState(VK_LWIN) & 0x8000) != 0 ||
                   (GetAsyncKeyState(VK_RWIN) & 0x8000) != 0;
        }

        private static bool IsVideoPlaying()
        {
            try
            {
                IntPtr hwnd = GetForegroundWindow();
                if (hwnd == IntPtr.Zero) return false;

                StringBuilder className = new StringBuilder(256);
                StringBuilder title = new StringBuilder(256);
                GetClassName(hwnd, className, className.Capacity);
                GetWindowText(hwnd, title, title.Capacity);

                string cls = className.ToString().ToLower();
                string ttl = title.ToString().ToLower();

                if (_excludedWindowTitles.Count > 0)
                {
                    string processName = "";
                    try
                    {
                        uint processId;
                        GetWindowThreadProcessId(hwnd, out processId);
                        using (var process = Process.GetProcessById((int)processId))
                        {
                            processName = process.ProcessName.ToLower();
                        }
                    }
                    catch
                    {
                        processName = "";
                    }

                    if (_excludedWindowTitles.Any(excluded =>
                    {
                        string excludedLower = excluded.ToLower();
                        return ttl.Contains(excludedLower) ||
                               cls.Contains(excludedLower) ||
                               (!string.IsNullOrEmpty(processName) && processName.Contains(excludedLower));
                    }))
                    {
                        return true;
                    }
                }

                bool matchTitle = _videoApps.Any(ind => ttl.Contains(ind));
                bool matchClass = _videoApps.Any(ind => cls.Contains(ind));
                bool hasPlaybackIndicator = _videoTitleIndicators.Any(ind => ttl.Contains(ind));

                if (matchTitle || matchClass || hasPlaybackIndicator)
                {
                    return true;
                }

                if (GetWindowRect(hwnd, out RECT rect))
                {
                    int screenWidth = GetSystemMetrics(SM_CXSCREEN);
                    int screenHeight = GetSystemMetrics(SM_CYSCREEN);

                    bool isFullscreen = rect.Left <= 0 && rect.Top <= 0 &&
                                        rect.Right >= screenWidth && rect.Bottom >= screenHeight;

                    if (isFullscreen && (matchClass || matchTitle))
                    {
                        return true;
                    }
                }

                return false;
            }
            catch
            {
                return false;
            }
        }

        private static readonly Dictionary<Screen, OverlayForm> _blackOverlays = new Dictionary<Screen, OverlayForm>();
        private static readonly List<IntPtr> _extraTaskbarWindows = new List<IntPtr>();

        private static void SetupOverlayWindows()
        {
            foreach (var screen in Screen.AllScreens)
            {
                var overlay = new OverlayForm();
                overlay.BackColor = Color.Black;
                overlay.FormBorderStyle = FormBorderStyle.None;
                overlay.Bounds = screen.Bounds;
                overlay.TopMost = true;
                overlay.ShowInTaskbar = false;
                overlay.StartPosition = FormStartPosition.Manual;
                overlay.Opacity = 1.0;
                overlay.KeyPreview = true;
                overlay.ClickThrough = false;
                overlay.Click += (s, e) => HideOverlays();
                overlay.KeyDown += (s, e) => HideOverlays();

                overlay.MouseEnter += (s, e) => Cursor.Hide();
                overlay.MouseLeave += (s, e) => Cursor.Show();

                overlay.VisibleChanged += (s, e) =>
                {
                    if (overlay.Visible)
                        Cursor.Hide();
                    else
                        Cursor.Show();
                };

                _overlays[screen] = overlay;
            }
        }

        private static void StartInactivityTimer()
        {
            _inactivityTimer = new Timer { Interval = 700 };
            _inactivityTimer.Tick += (s, e) => CheckInactivity();
            _inactivityTimer.Start();
        }

        private static void CheckDesktopInteraction()
        {
            if (!GetCursorPos(out Point currentCursorPos)) return;

            bool isOverDesktop = IsUserInteractingWithDesktop(currentCursorPos);

            if (isOverDesktop)
            {
                if (_lastCursorPos != currentCursorPos)
                {
                    _lastActiveTime = DateTime.Now;
                    _lastCursorPos = currentCursorPos;
                }

                var inactiveTime = DateTime.Now - _lastActiveTime;
                if (inactiveTime >= InactivityThreshold)
                {
                    if (!_desktopIconsHidden)
                        HideDesktopIcons();
                }
                else
                {
                    if (_desktopIconsHidden)
                        ShowDesktopIcons();
                }
            }
            else
            {
                _lastActiveTime = DateTime.Now;
                if (!_desktopIconsHidden)
                    HideDesktopIcons();
            }
        }

        private static bool IsUserInteractingWithDesktop(Point cursorPos)
        {
            var windowUnderCursor = WindowFromPoint(cursorPos);
            if (windowUnderCursor == IntPtr.Zero) return false;

            var rootWindow = GetAncestor(windowUnderCursor, GA_ROOT);

            var className = GetWindowClassName(rootWindow);

            return IsDesktopRelatedWindow(className, rootWindow);
        }

        private static bool IsDesktopRelatedWindow(string className, IntPtr hWnd)
        {
            var desktopClasses = new[]
            {
                "Progman",
                "WorkerW",
                "SHELLDLL_DefView",
                "SysListView32"
            };

            return desktopClasses.Contains(className);
        }

        private static void CheckInactivity()
        {
            double idleSeconds = GetIdleTimeSeconds();
            _isVideoPlaying = IsVideoPlaying();

            foreach (var kvp in _overlays)
            {
                var screen = kvp.Key;
                var overlay = kvp.Value;
                var setting = _monitorSettings[screen.DeviceName];
                if (setting.Enabled && idleSeconds >= setting.TimeoutSeconds && !_isVideoPlaying)
                {
                    if (!overlay.Visible)
                        overlay.Show();
                }
                else
                {
                    if (overlay.Visible)
                        overlay.Hide();
                }
            }

            if (_drawBlackOverlay)
            {
                UpdateBlackOverlays();
            }

            if (_desktopIconsHidingEnabled)
            {
                CheckDesktopInteraction();
                if (idleSeconds >= _desktopIconsTimeoutSeconds)
                {
                    HideDesktopIcons();
                }
            }

            if (_drawBlackOverlayEnabled)
            {
                if (idleSeconds >= _drawBlackOverlayEnabledTimeoutSeconds)
                {
                    UpdateOverlayForActiveWindow();
                    CheckCursorForOverlayFade();
                }
                else
                {
                    if (_drawBlackOverlay)
                    {
                        _overlayUpdateCts?.Cancel();
                        _overlayUpdateCts = null;
                        _drawBlackOverlay = false;
                        _windowThatTriggeredOverlay = IntPtr.Zero;
                        _overlayFaded = false;
                        HideBlackOverlays();
                    }
                }
            }

            if (_screenOffEnabled)
            {
                if (idleSeconds >= _displayOffTimeoutSeconds && !_screenOff)
                {
                    TurnOffDisplay();
                }
            }
        }

        private static bool GetExtendedFrameBounds(IntPtr hwnd, out RECT rect)
        {
            rect = new RECT();
            int hr = DwmGetWindowAttribute(hwnd, DWMWA_EXTENDED_FRAME_BOUNDS, out rect, Marshal.SizeOf(typeof(RECT)));
            return hr == 0;
        }

        private static void UpdateBlackOverlays()
        {
            if (!_drawBlackOverlay || _windowThatTriggeredOverlay == IntPtr.Zero)
                return;

            if (!GetExtendedFrameBounds(_windowThatTriggeredOverlay, out RECT windowRect))
            {
                if (!GetWindowRect(_windowThatTriggeredOverlay, out windowRect))
                    return;
            }

            _targetActiveWindowRect = new Rectangle(
                windowRect.Left,
                windowRect.Top,
                windowRect.Right - windowRect.Left,
                windowRect.Bottom - windowRect.Top);

            bool windowIsMoving = !_targetActiveWindowRect.Equals(_previousTargetRect);
            _previousTargetRect = _targetActiveWindowRect;

            Rectangle newOverlayRect;

            if (_enableInterpolation && !windowIsMoving)
            {
                newOverlayRect = LerpRect(_currentActiveWindowRect, _targetActiveWindowRect, 0.2f);
            }
            else
            {
                newOverlayRect = _targetActiveWindowRect;
            }

            if (newOverlayRect == _lastRenderedOverlayRect)
                return;

            _lastRenderedOverlayRect = newOverlayRect;
            _currentActiveWindowRect = newOverlayRect;

            foreach (var kvp in _blackOverlays)
            {
                var screen = kvp.Key;
                var overlay = kvp.Value;
                Rectangle screenBounds = screen.Bounds;

                Rectangle relativeRect = new Rectangle(
                    newOverlayRect.Left - screenBounds.Left,
                    newOverlayRect.Top - screenBounds.Top,
                    newOverlayRect.Width,
                    newOverlayRect.Height);

                Region region = new Region(new Rectangle(0, 0, overlay.Width, overlay.Height));

                if (_overlayRoundedCorners)
                {
                    Region roundedWindowRegion = CreateRoundedRegion(relativeRect, 6);
                    region.Exclude(roundedWindowRegion);
                }
                else
                {
                    Region rectangularWindowRegion = new Region(relativeRect);
                    region.Exclude(rectangularWindowRegion);
                }

                if (overlay.Region != null)
                    overlay.Region.Dispose();

                overlay.Region = region;
            }
        }

        private static Rectangle LerpRect(Rectangle from, Rectangle to, float t)
        {
            return new Rectangle(
                (int)(from.X + (to.X - from.X) * t),
                (int)(from.Y + (to.Y - from.Y) * t),
                (int)(from.Width + (to.Width - from.Width) * t),
                (int)(from.Height + (to.Height - from.Height) * t)
            );
        }

        private static void CheckCursorForOverlayFade()
        {
            if (!_drawBlackOverlay || _windowThatTriggeredOverlay == IntPtr.Zero)
                return;

            if (!GetExtendedFrameBounds(_windowThatTriggeredOverlay, out RECT rect))
                return;

            Point cursor;
            if (!GetCursorPos(out cursor)) return;

            bool cursorInside = cursor.X >= rect.Left &&
                                cursor.X <= rect.Right &&
                                cursor.Y >= rect.Top &&
                                cursor.Y <= rect.Bottom;

            if (!cursorInside && !_overlayFaded)
            {
                foreach (var overlay in _blackOverlays.Values)
                {
                    if (!overlay.IsDisposed)
                        overlay.Opacity = _overlayFadedOpacity;
                }
                _overlayFaded = true;
            }
            else if (cursorInside && _overlayFaded)
            {
                foreach (var overlay in _blackOverlays.Values)
                {
                    if (!overlay.IsDisposed)
                        overlay.Opacity = _overlayOpacity;
                }
                _overlayFaded = false;
            }
        }

        private static int GetScreenRefreshRate(Screen screen)
        {
            DEVMODE devMode = new DEVMODE();
            devMode.dmSize = (ushort)Marshal.SizeOf(typeof(DEVMODE));

            if (EnumDisplaySettings(screen.DeviceName, ENUM_CURRENT_SETTINGS, ref devMode))
            {
                int refreshRate = (int)devMode.dmDisplayFrequency;
                if (refreshRate > 0)
                    return refreshRate;
            }

            return 60;
        }

        private static async Task StartOverlayRealtimeUpdates()
        {
            _overlayUpdateCts?.Cancel();
            _overlayUpdateCts = new CancellationTokenSource();
            var token = _overlayUpdateCts.Token;

            int refreshRate = GetScreenRefreshRate(Screen.PrimaryScreen);
            int fastDelay = Math.Max(5, 1000 / refreshRate);
            int slowDelay = 500;

            Point lastCursor = new Point();
            _lastWindowBounds = Rectangle.Empty;

            int activityFrames = 0;
            const int maxActivityFrames = 100;

            try
            {
                while (!token.IsCancellationRequested)
                {
                    bool updated = false;

                    IntPtr currentForeground = GetForegroundWindow();
                    if (currentForeground == _windowThatTriggeredOverlay)
                    {
                        if (GetWindowRect(currentForeground, out RECT currentRect))
                        {
                            Rectangle currentBounds = new Rectangle(
                                currentRect.Left,
                                currentRect.Top,
                                currentRect.Right - currentRect.Left,
                                currentRect.Bottom - currentRect.Top);

                            if (!_lastWindowBounds.Equals(currentBounds))
                            {
                                UpdateBlackOverlays();
                                _lastWindowBounds = currentBounds;
                                updated = true;
                            }
                        }
                    }
                    else
                    {
                        UpdateOverlayForActiveWindow();
                        updated = true;
                    }

                    Point currentCursor;
                    if (_drawBlackOverlay && GetCursorPos(out currentCursor) && currentCursor != lastCursor)
                    {
                        bool wasInside = IsCursorInsideWindow(_windowThatTriggeredOverlay, lastCursor);
                        bool isNowInside = IsCursorInsideWindow(_windowThatTriggeredOverlay, currentCursor);

                        if (wasInside != isNowInside)
                        {
                            CheckCursorForOverlayFade();
                            updated = true;
                        }

                        lastCursor = currentCursor;
                    }

                    if (updated)
                    {
                        activityFrames = maxActivityFrames;
                        await Task.Delay(fastDelay, token);
                    }
                    else if (activityFrames > 0)
                    {
                        activityFrames--;
                        await Task.Delay(fastDelay, token);
                    }
                    else
                    {
                        await Task.Delay(slowDelay, token);
                    }
                }
            }
            catch (TaskCanceledException)
            {
            }
        }

        private static bool IsCursorInsideWindow(IntPtr hwnd, Point cursor)
        {
            if (!GetExtendedFrameBounds(hwnd, out RECT rect))
                return false;

            return cursor.X >= rect.Left &&
                   cursor.X <= rect.Right &&
                   cursor.Y >= rect.Top &&
                   cursor.Y <= rect.Bottom;
        }

        private static Region CreateRoundedRegion(Rectangle bounds, int radius)
        {
            GraphicsPath path = new GraphicsPath();

            int diameter = radius * 2;
            Size size = new Size(diameter, diameter);
            Rectangle arc = new Rectangle(bounds.Location, size);

            path.AddArc(arc, 180, 90);

            arc.X = bounds.Right - diameter;
            path.AddArc(arc, 270, 90);

            arc.Y = bounds.Bottom - diameter;
            path.AddArc(arc, 0, 90);

            arc.X = bounds.Left;
            path.AddArc(arc, 90, 90);

            path.CloseFigure();
            return new Region(path);
        }

        private static string GetWindowClassName(IntPtr hWnd)
        {
            var className = new StringBuilder(256);
            GetClassName(hWnd, className, className.Capacity);
            return className.ToString();
        }

        private static void CreateOrUpdateBlackOverlays()
        {
            if (_windowThatTriggeredOverlay == IntPtr.Zero) return;

            if (!GetWindowRect(_windowThatTriggeredOverlay, out RECT activeWindowRect)) return;

            foreach (var screen in Screen.AllScreens)
            {
                Rectangle screenBounds = screen.Bounds;

                OverlayForm overlay;
                if (!_blackOverlays.TryGetValue(screen, out overlay) || overlay.IsDisposed)
                {
                    overlay = new OverlayForm();
                    overlay.FormBorderStyle = FormBorderStyle.None;
                    overlay.ShowInTaskbar = false;
                    overlay.StartPosition = FormStartPosition.Manual;
                    overlay.TopMost = true;
                    overlay.BackColor = Color.Black;
                    overlay.Opacity = _overlayOpacity;
                    overlay.Bounds = screenBounds;
                    overlay.ClickThrough = true;
                    overlay.Show();
                    _blackOverlays[screen] = overlay;
                }
                else
                {
                    overlay.Bounds = screenBounds;
                    overlay.Opacity = _overlayOpacity;
                    overlay.Show();
                }
            }

            _lastActiveWindowRect = Rectangle.Empty;
            UpdateBlackOverlays();
        }

        private static void UpdateOverlayForActiveWindow()
        {
            if (!_drawBlackOverlayEnabled)
                return;

            IntPtr currentForeground = GetForegroundWindow();
            if (currentForeground == IntPtr.Zero)
            {
                HideBlackOverlays();
                _windowThatTriggeredOverlay = IntPtr.Zero;
                _drawBlackOverlay = false;
                return;
            }

            if (currentForeground != _windowThatTriggeredOverlay)
            {
                _windowThatTriggeredOverlay = currentForeground;

                if (!_drawBlackOverlay)
                {
                    CreateOrUpdateBlackOverlays();
                    _ = StartOverlayRealtimeUpdates();
                    _drawBlackOverlay = true;
                }
                else
                {
                    UpdateBlackOverlays();
                }
            }
            else if (_drawBlackOverlay)
            {
                UpdateBlackOverlays();
            }
        }

        public class OverlayForm : Form
        {
            private bool _clickThrough = false;

            [Browsable(false)]
            [DesignerSerializationVisibility(DesignerSerializationVisibility.Hidden)]
            public bool ClickThrough
            {
                get => _clickThrough;
                set
                {
                    if (_clickThrough != value)
                    {
                        _clickThrough = value;
                        UpdateWindowStyle();
                    }
                }
            }

            protected override CreateParams CreateParams
            {
                get
                {
                    CreateParams cp = base.CreateParams;
                    cp.ExStyle |= 0x80;
                    cp.ExStyle |= 0x08000000;

                    if (_clickThrough)
                    {
                        cp.ExStyle |= 0x20;
                    }

                    return cp;
                }
            }

            protected override bool ShowWithoutActivation => true;

            private void UpdateWindowStyle()
            {
                if (IsHandleCreated)
                {
                    int exStyle = GetWindowLong(Handle, -20);
                    if (_clickThrough)
                        exStyle |= 0x20;
                    else
                        exStyle &= ~0x20;

                    SetWindowLong(Handle, -20, exStyle);
                }
            }
        }

        private class DarkColorTable : ProfessionalColorTable
        {
            public override Color ToolStripDropDownBackground => Color.FromArgb(32, 32, 32);
            public override Color ImageMarginGradientBegin => Color.FromArgb(32, 32, 32);
            public override Color ImageMarginGradientMiddle => Color.FromArgb(32, 32, 32);
            public override Color ImageMarginGradientEnd => Color.FromArgb(32, 32, 32);
            public override Color MenuItemBorder => Color.FromArgb(70, 70, 70);
            public override Color MenuItemSelected => Color.FromArgb(60, 60, 60);
            public override Color MenuItemSelectedGradientBegin => Color.FromArgb(60, 60, 60);
            public override Color MenuItemSelectedGradientEnd => Color.FromArgb(60, 60, 60);
            public override Color MenuStripGradientBegin => Color.FromArgb(32, 32, 32);
            public override Color MenuStripGradientEnd => Color.FromArgb(32, 32, 32);
            public override Color ToolStripBorder => Color.FromArgb(60, 60, 60);
            public override Color ToolStripGradientBegin => Color.FromArgb(32, 32, 32);
            public override Color ToolStripGradientMiddle => Color.FromArgb(32, 32, 32);
            public override Color ToolStripGradientEnd => Color.FromArgb(32, 32, 32);
            public override Color SeparatorDark => Color.FromArgb(80, 80, 80);
            public override Color SeparatorLight => Color.FromArgb(80, 80, 80);
        }

        private class DarkRenderer : ToolStripProfessionalRenderer
        {
            public DarkRenderer() : base(new DarkColorTable())
            {
            }

            protected override void OnRenderItemText(ToolStripItemTextRenderEventArgs e)
            {
                e.TextColor = Color.White;
                base.OnRenderItemText(e);
            }

            protected override void OnRenderMenuItemBackground(ToolStripItemRenderEventArgs e)
            {
                Rectangle rect = new Rectangle(Point.Empty, e.Item.Bounds.Size);
                Color color = e.Item.Selected ? Color.FromArgb(60, 60, 60) : Color.FromArgb(32, 32, 32);
                using (SolidBrush brush = new SolidBrush(color))
                {
                    e.Graphics.FillRectangle(brush, rect);
                }
            }

            protected override void OnRenderArrow(ToolStripArrowRenderEventArgs e)
            {
                e.ArrowColor = Color.White;
                base.OnRenderArrow(e);
            }
        }

        private static void HideBlackOverlays()
        {
            foreach (var overlay in _blackOverlays.Values)
            {
                if (!overlay.IsDisposed)
                {
                    overlay.Hide();
                    overlay.Region = null;
                }
            }
        }

        private static void HideStartButtonsWithStartAllBack()
        {
            _extraTaskbarWindows.Clear();
            Rectangle primaryBounds = Screen.PrimaryScreen.Bounds;

            EnumWindows((hWnd, lParam) =>
            {
                if (!IsWindowVisible(hWnd))
                    return true;

                if (!GetWindowRect(hWnd, out RECT r))
                    return true;

                int width = r.Right - r.Left;
                int height = r.Bottom - r.Top;

                if (width < 24 || width > 128 || height < 24 || height > 128)
                    return true;

                if (r.Bottom < primaryBounds.Bottom - 5)
                    return true;

                string cls = GetWindowClassName(hWnd);
                if (cls == "Shell_TrayWnd" || cls == "Shell_SecondaryTrayWnd")
                    return true;

                uint pid;
                GetWindowThreadProcessId(hWnd, out pid);
                string processName;
                try
                {
                    using (var p = Process.GetProcessById((int)pid))
                    {
                        processName = p.ProcessName.ToLower();
                    }
                }
                catch
                {
                    return true;
                }

                if (processName != "explorer")
                    return true;

                _extraTaskbarWindows.Add(hWnd);
                ShowWindow(hWnd, SW_HIDE);
                return true;
            }, IntPtr.Zero);
        }

        private static void ShowStartButtonsWithStartAllBack()
        {
            foreach (var hWnd in _extraTaskbarWindows.ToList())
            {
                if (IsWindow(hWnd))
                    ShowWindow(hWnd, SW_SHOW);
            }
            _extraTaskbarWindows.Clear();
        }

        private static void HideTaskbarAndDesktop()
        {
            if (_taskbarHidden) return;

            var taskbar = FindWindow("Shell_TrayWnd", null);

            if (!_workAreaStored)
            {
                SystemParametersInfo(SPI_GETWORKAREA, 0, ref _originalWorkArea, 0);
                _workAreaStored = true;
            }

            ShowWindow(taskbar, SW_HIDE);
            HideStartButtonsWithStartAllBack();

            RECT unchanged = _originalWorkArea;
            SystemParametersInfo(SPI_SETWORKAREA, 0, ref unchanged, SPIF_SENDCHANGE);

            _taskbarHidden = true;
        }

        private static void ShowTaskbarAndDesktop()
        {
            if (!_taskbarHidden) return;

            var taskbar = FindWindow("Shell_TrayWnd", null);
            ShowWindow(taskbar, SW_SHOW);
            ShowStartButtonsWithStartAllBack();

            if (_workAreaStored)
                SystemParametersInfo(SPI_SETWORKAREA, 0, ref _originalWorkArea, SPIF_SENDCHANGE);

            _taskbarHidden = false;
        }

        private static void HideDesktopIcons()
        {
            if (_desktopIconsHidden || !IsDesktopVisible()) return;
            var hWndDesktop = GetDesktopListView();
            if (hWndDesktop != IntPtr.Zero)
                ShowWindow(hWndDesktop, SW_HIDE);
            _desktopIconsHidden = true;
        }

        private static void ShowDesktopIcons()
        {
            if (!_desktopIconsHidden) return;

            var hWndDesktop = GetDesktopListView();
            if (hWndDesktop != IntPtr.Zero)
            {
                ShowWindow(hWndDesktop, SW_SHOW);
                UpdateWindow(hWndDesktop);
                RedrawWindow(hWndDesktop, IntPtr.Zero, IntPtr.Zero, RDW_INVALIDATE | RDW_UPDATENOW | RDW_ALLCHILDREN);
            }

            _desktopIconsHidden = false;
        }

        private static IntPtr GetDesktopListView()
        {
            IntPtr hShellViewWin = IntPtr.Zero;
            IntPtr hProgman = FindWindow("Progman", null);
            if (hProgman != IntPtr.Zero)
            {
                IntPtr hDesktopWnd = FindWindowEx(hProgman, IntPtr.Zero, "SHELLDLL_DefView", null);
                if (hDesktopWnd == IntPtr.Zero)
                {
                    IntPtr hWorkerW = FindWindowEx(IntPtr.Zero, IntPtr.Zero, "WorkerW", null);
                    while (hWorkerW != IntPtr.Zero && hDesktopWnd == IntPtr.Zero)
                    {
                        hDesktopWnd = FindWindowEx(hWorkerW, IntPtr.Zero, "SHELLDLL_DefView", null);
                        hWorkerW = FindWindowEx(IntPtr.Zero, hWorkerW, "WorkerW", null);
                    }
                }
                if (hDesktopWnd != IntPtr.Zero)
                {
                    hShellViewWin = FindWindowEx(hDesktopWnd, IntPtr.Zero, "SysListView32", "FolderView");
                }
            }
            return hShellViewWin;
        }

        private static bool IsDesktopVisible()
        {
            var foregroundWindow = GetForegroundWindow();
            if (foregroundWindow == IntPtr.Zero) return true;

            var className = GetWindowClassName(foregroundWindow);
            if (className == "Progman")
            {
                return true;
            }

            if (GetWindowRect(foregroundWindow, out RECT windowRect))
            {
                var screenWidth = GetSystemMetrics(SM_CXSCREEN);
                var screenHeight = GetSystemMetrics(SM_CYSCREEN);

                bool isFullscreen = windowRect.Left <= 0 &&
                                    windowRect.Top <= 0 &&
                                    windowRect.Right >= screenWidth &&
                                    windowRect.Bottom >= screenHeight;

                return !isFullscreen;
            }
            return true;
        }

        private static void HideDesktopIconsIfNeeded()
        {
            if (_desktopIconsHidden) return;

            if (IsDesktopVisible())
            {
                var hWndDesktop = GetDesktopListView();
                if (hWndDesktop != IntPtr.Zero)
                {
                    ShowWindow(hWndDesktop, SW_HIDE);
                    _desktopIconsHidden = true;
                }
            }
        }

        private static void ShowDesktopIconsIfNeeded()
        {
            if (!_desktopIconsHidden) return;

            var hWndDesktop = GetDesktopListView();
            if (hWndDesktop != IntPtr.Zero)
            {
                ShowWindow(hWndDesktop, SW_SHOW);
                _desktopIconsHidden = false;
            }
        }

        private static bool HasVisibleWindows()
        {
            var visibleWindows = new List<IntPtr>();

            EnumWindows((hWnd, lParam) =>
            {
                if (IsWindowVisible(hWnd) && !IsIconic(hWnd))
                {
                    if (GetWindowRect(hWnd, out RECT rect))
                    {
                        if (rect.Right - rect.Left > 100 && rect.Bottom - rect.Top > 100)
                        {
                            visibleWindows.Add(hWnd);
                        }
                    }
                }
                return true;
            }, IntPtr.Zero);

            return visibleWindows.Count > 0;
        }

        private static bool ShouldHideDesktopIcons()
        {
            if (!IsDesktopVisible()) return false;

            if (HasVisibleWindows()) return false;

            return true;
        }

        private static void ManageDesktopIcons()
        {
            if (ShouldHideDesktopIcons())
            {
                HideDesktopIconsIfNeeded();
            }
            else
            {
                ShowDesktopIconsIfNeeded();
            }
        }

        private static void StartDesktopMonitoring()
        {
            if (_hookHandle != IntPtr.Zero)
                return;

            _hookHandle = SetWinEventHook(
                EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_FOREGROUND,
                IntPtr.Zero, _winEventProc, 0, 0,
                WINEVENT_OUTOFCONTEXT);
        }

        private static void StopDesktopMonitoring()
        {
            if (_hookHandle != IntPtr.Zero)
            {
                UnhookWinEvent(_hookHandle);
                _hookHandle = IntPtr.Zero;
            }
        }

        private static void WinEventProc(IntPtr hWinEventHook, uint eventType,
            IntPtr hwnd, int idObject, int idChild, uint dwEventThread, uint dwmsEventTime)
        {
            if (eventType == EVENT_SYSTEM_FOREGROUND)
            {
                Task.Delay(100).ContinueWith(_ => ManageDesktopIcons());
            }
        }

        private static double GetIdleTimeSeconds()
        {
            LASTINPUTINFO info = new LASTINPUTINFO();
            info.cbSize = (uint)Marshal.SizeOf(info);
            if (GetLastInputInfo(ref info))
            {
                uint tickCount = (uint)Environment.TickCount;
                uint lastInput = info.dwTime;
                uint diff = tickCount - lastInput;
                return diff / 1000.0;
            }
            return 0;
        }

        private static void HideOverlays()
        {
            foreach (var overlay in _overlays.Values)
            {
                if (overlay.Visible)
                    overlay.Hide();
            }
        }

        private static void TurnOffDisplay()
        {
            if (_screenOff) return;

            if (IsVideoPlaying())
            {
                return;
            }

            SendMessage(HWND_BROADCAST, WM_SYSCOMMAND, (IntPtr)SC_MONITORPOWER, (IntPtr)2);
            _screenOff = true;
        }

        private static void TurnOnDisplay()
        {
            if (!_screenOff) return;
            SendMessage(HWND_BROADCAST, WM_SYSCOMMAND, (IntPtr)SC_MONITORPOWER, (IntPtr)(-1));
            _screenOff = false;
        }

        private static void ExitApplication()
        {
            SaveSettings();
            StopDesktopMonitoring();

            if (_desktopIconsHidden)
                ShowDesktopIconsIfNeeded();

            if (_taskbarHidden)
                ShowTaskbarAndDesktop();

            if (_screenOff)
                TurnOnDisplay();

            _overlayUpdateCts?.Cancel();

            _trayIcon?.Dispose();
            foreach (var overlay in _overlays.Values)
                overlay?.Dispose();

            foreach (var overlay in _blackOverlays.Values)
                overlay?.Dispose();

            Application.Exit();
        }
    }
}
