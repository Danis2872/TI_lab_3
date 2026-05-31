using Microsoft.Win32;
using System;
using System.IO;
using System.Numerics;
using System.Text;
using System.Windows;
using System.Windows.Controls;

namespace RsaCryptoApp
{
    public partial class MainWindow : Window
    {
        private string _selectedFilePath = null;

        private BigInteger _p = 0, _q = 0, _n = 0, _b = 0;

        public MainWindow()
        {
            InitializeComponent();
            UpdateMode();
        }

        // ─── БЫСТРОЕ ВОЗВЕДЕНИЕ В СТЕПЕНЬ ПО МОДУЛЮ ─────────────────────────────
        private static BigInteger FastPow(BigInteger a, BigInteger z, BigInteger n)
        {
            if (n == 1) return 0;
            BigInteger result = 1;
            a = a % n;
            while (z > 0)
            {
                if (z % 2 == 1)
                    result = result * a % n;
                z >>= 1;
                a = a * a % n;
            }
            return result;
        }

        // ─── РАСШИРЕННЫЙ АЛГОРИТМ ЕВКЛИДА ────────────────────────────────────────
        private static BigInteger ExtendedGcd(BigInteger a, BigInteger b, out BigInteger x, out BigInteger y)
        {
            BigInteger d0 = a, d1 = b;
            BigInteger x0 = 1, x1 = 0;
            BigInteger y0 = 0, y1 = 1;

            while (d1 > 0)
            {
                BigInteger q  = d0 / d1;
                BigInteger d2 = d0 % d1;
                BigInteger x2 = x0 - q * x1;
                BigInteger y2 = y0 - q * y1;

                d0 = d1; d1 = d2;
                x0 = x1; x1 = x2;
                y0 = y1; y1 = y2;
            }
            x = x0;
            y = y0;
            return d0;
        }

        // ─── ПРОВЕРКА ПРОСТОТЫ ────────────────────────────────────────────────────
        private static bool IsPrime(BigInteger n)
        {
            if (n < 2) return false;
            if (n == 2) return true;
            if (n % 2 == 0) return false;
            for (BigInteger i = 3; i * i <= n; i += 2)
                if (n % i == 0) return false;
            return true;
        }

        // ─── КВАДРАТНЫЙ КОРЕНЬ ПО МОДУЛЮ ПРОСТОГО (p ≡ 3 mod 4) ─────────────────
        private static BigInteger SqrtMod(BigInteger a, BigInteger p)
        {
            return FastPow(a, (p + 1) / 4, p);
        }

        // ─── ЧЕТЫРЕ КОРНЯ √D mod n (КТО + расширенный Евклид) ───────────────────
        private static BigInteger[] SqrtModN(BigInteger D, BigInteger p, BigInteger q, BigInteger n)
        {
            BigInteger mp = SqrtMod(D % p, p);
            BigInteger mq = SqrtMod(D % q, q);

            BigInteger yp, yq;
            ExtendedGcd(p, q, out yp, out yq);

            BigInteger[] results = new BigInteger[4];

            // Все 4 комбинации знаков (±mp, ±mq)
            results[0] = (yp * p % n * mq + yq * q % n * mp) % n;
            if (results[0] < 0) results[0] += n;

            results[1] = (yp * p % n * (-mq) + yq * q % n * mp) % n;
            if (results[1] < 0) results[1] += n;

            results[2] = (yp * p % n * mq + yq * q % n * (-mp)) % n;
            if (results[2] < 0) results[2] += n;

            results[3] = (yp * p % n * (-mq) + yq * q % n * (-mp)) % n;
            if (results[3] < 0) results[3] += n;

            return results;
        }

        // ─── ШИФРОВАНИЕ БЛОКА: c = m*(m+b) mod n ────────────────────────────────
        private static BigInteger RabinEncrypt(BigInteger m, BigInteger b, BigInteger n)
        {
            return m * (m + b) % n;
        }

        // ─── ДЕШИФРОВАНИЕ БЛОКА ───────────────────────────────────────────────────
        private static BigInteger RabinDecrypt(BigInteger c, BigInteger b, BigInteger p, BigInteger q, BigInteger n)
        {
            BigInteger D = (b * b + 4 * c) % n;
            BigInteger[] roots = SqrtModN(D, p, q, n);

            BigInteger inv2, dummy;
            ExtendedGcd(2, n, out inv2, out dummy);
            inv2 = ((inv2 % n) + n) % n;

            BigInteger found = -1;
            foreach (var di in roots)
            {
                BigInteger mi = ((di - b) % n + n) % n * inv2 % n;
                if (mi < 256)
                {
                    if (found == -1)
                        found = mi;
                    else if (found != mi)
                        throw new Exception(
                            $"Неоднозначная расшифровка (c={c}): найдено несколько корней < 256 ({found} и {mi}). " +
                            $"Увеличьте p и q (рекомендуется p,q > 3511, b < 10533).");
                }
            }

            return found;
        }

        // ─── ВАЛИДАЦИЯ ПАРАМЕТРОВ ────────────────────────────────────────────────
        private bool TryComputeParams(out string error)
        {
            error = "";
            _p = _q = _n = _b = 0;

            if (rbDecrypt.IsChecked == true)
            {
                if (!BigInteger.TryParse(txtP.Text.Trim(), out _p) || _p < 2)
                { error = "p: введите простое число ≥ 2"; return false; }
                if (!IsPrime(_p))
                { error = $"p = {_p} не является простым числом!"; return false; }

                if (!BigInteger.TryParse(txtQ.Text.Trim(), out _q) || _q < 2)
                { error = "q: введите простое число ≥ 2"; return false; }
                if (!IsPrime(_q))
                { error = $"q = {_q} не является простым числом!"; return false; }

                if (_p % 4 != 3)
                { error = $"p = {_p}: условие p ≡ 3 (mod 4) не выполнено!"; return false; }
                if (_q % 4 != 3)
                { error = $"q = {_q}: условие q ≡ 3 (mod 4) не выполнено!"; return false; }
                if (_p == _q)
                { error = "p и q должны быть различными!"; return false; }

                _n = _p * _q;

                if (!BigInteger.TryParse(txtB.Text.Trim(), out _b) || _b < 0)
                { error = "b: введите целое число ≥ 0"; return false; }
                if (_b >= _n)
                { error = $"b должно быть < n = {_n}"; return false; }

                return true;
            }

            // Шифрование
            if (!BigInteger.TryParse(txtP.Text.Trim(), out _p) || _p < 2)
            { error = "p: введите простое число"; return false; }
            if (!IsPrime(_p))
            { error = $"p = {_p} не является простым числом!"; return false; }
            if (_p % 4 != 3)
            { error = $"p = {_p}: нарушено условие p ≡ 3 (mod 4). Примеры: 3, 7, 11, 19, 23, 31, 43..."; return false; }

            if (!BigInteger.TryParse(txtQ.Text.Trim(), out _q) || _q < 2)
            { error = "q: введите простое число"; return false; }
            if (!IsPrime(_q))
            { error = $"q = {_q} не является простым числом!"; return false; }
            if (_q % 4 != 3)
            { error = $"q = {_q}: нарушено условие q ≡ 3 (mod 4). Примеры: 3, 7, 11, 19, 23, 31, 43..."; return false; }
            if (_p == _q)
            { error = "p и q должны быть различными!"; return false; }

            _n = _p * _q;
            if (_n <= 255)
            { error = $"n = p*q = {_n} должно быть > 255 для шифрования байтов (0..255)"; return false; }

            if (!BigInteger.TryParse(txtB.Text.Trim(), out _b) || _b < 0)
            { error = "b: введите целое число ≥ 0"; return false; }
            if (_b >= _n)
            { error = $"b должно быть < n = {_n}"; return false; }

            return true;
        }

        // ─── ОБНОВЛЕНИЕ ПОЛЯ n ───────────────────────────────────────────────────
        private void ParamChanged(object sender, TextChangedEventArgs e)
        {
            if (txtP == null || txtQ == null) return;
            RefreshComputedFields();
        }

        private void RefreshComputedFields()
        {
            txtError.Text = "";

            if (BigInteger.TryParse(txtP.Text.Trim(), out BigInteger p) &&
                BigInteger.TryParse(txtQ.Text.Trim(), out BigInteger q) &&
                IsPrime(p) && IsPrime(q) && p != q &&
                p % 4 == 3 && q % 4 == 3)
            {
                txtN.Text = (p * q).ToString();
            }
            else
            {
                if (!string.IsNullOrWhiteSpace(txtP.Text) || !string.IsNullOrWhiteSpace(txtQ.Text))
                    txtN.Text = "—";
            }

            UpdateProcessButton();
        }

        // ─── СМЕНА РЕЖИМА ─────────────────────────────────────────────────────────
        private void ModeChanged(object sender, RoutedEventArgs e) => UpdateMode();

        private void UpdateMode()
        {
            if (txtP == null) return;

            if (rbEncrypt?.IsChecked == true)
            {
                lblResult.Text = "ЗАШИФРОВАННЫЙ ФАЙЛ (байты в dec)";
                btnProcess.Content = "🔒 Зашифровать";
            }
            else
            {
                lblResult.Text = "РАСШИФРОВАННЫЙ ФАЙЛ (байты в dec)";
                btnProcess.Content = "🔓 Расшифровать";
            }

            memoSource.Clear();
            memoResult.Clear();
            txtError.Text = "";
            RefreshComputedFields();
        }

        private void UpdateProcessButton()
        {
            if (btnProcess == null) return;
            btnProcess.IsEnabled = (_selectedFilePath != null);
        }

        // ─── ОТКРЫТЬ ФАЙЛ ─────────────────────────────────────────────────────────
        private void BtnOpenFile_Click(object sender, RoutedEventArgs e)
        {
            var dlg = new OpenFileDialog
            {
                Title = "Выберите файл для обработки",
                Filter = "Все файлы (*.*)|*.*"
            };

            if (dlg.ShowDialog() == true)
            {
                _selectedFilePath = dlg.FileName;
                string name = Path.GetFileName(_selectedFilePath);
                long size = new FileInfo(_selectedFilePath).Length;
                txtStatus.Text = $"📄 {name}  |  {size} байт  |  {_selectedFilePath}";

                LoadSourceFile();
                memoResult.Clear();
                UpdateProcessButton();
            }
        }

        private void LoadSourceFile()
        {
            if (_selectedFilePath == null) return;
            try
            {
                byte[] data = File.ReadAllBytes(_selectedFilePath);
                int showCount = Math.Min(data.Length, 2048);
                var sb = new StringBuilder();
                for (int i = 0; i < showCount; i++)
                {
                    sb.Append(data[i]);
                    if (i < showCount - 1) sb.Append(' ');
                    if ((i + 1) % 20 == 0) sb.AppendLine();
                }
                if (data.Length > 2048)
                    sb.AppendLine($"\n... (показаны первые 2048 из {data.Length} байт)");

                memoSource.Text = sb.ToString();
            }
            catch (Exception ex)
            {
                txtError.Text = $"Ошибка чтения файла: {ex.Message}";
            }
        }

        // ─── ЗАПУСК ШИФРОВАНИЯ / ДЕШИФРОВАНИЯ ────────────────────────────────────
        private void BtnProcess_Click(object sender, RoutedEventArgs e)
        {
            txtError.Text = "";

            if (_selectedFilePath == null)
            { txtError.Text = "Файл не выбран!"; return; }

            if (!TryComputeParams(out string validError))
            { txtError.Text = validError; return; }

            txtN.Text = _n.ToString();

            try
            {
                if (rbEncrypt.IsChecked == true)
                    EncryptFile();
                else
                    DecryptFile();
            }
            catch (Exception ex)
            {
                txtError.Text = $"Ошибка: {ex.Message}";
            }
        }

        // ─── ШИФРОВАНИЕ ФАЙЛА ─────────────────────────────────────────────────────
        private void EncryptFile()
        {
            byte[] inputData = File.ReadAllBytes(_selectedFilePath);

            int bitLength = (int)Math.Floor(BigInteger.Log(_n, 2)) + 1;
            int blockSize = (bitLength + 7) / 8;
            if (blockSize < 2) blockSize = 2;

            byte[] outputData = new byte[inputData.Length * blockSize];

            var sbResult = new StringBuilder();
            int showCount = Math.Min(inputData.Length, 512);

            for (int i = 0; i < inputData.Length; i++)
            {
                BigInteger mi = inputData[i];
                BigInteger ci = RabinEncrypt(mi, _b, _n);

                byte[] ciBytes = ci.ToByteArray();
                for (int j = 0; j < blockSize; j++)
                    outputData[i * blockSize + j] = j < ciBytes.Length ? ciBytes[j] : (byte)0;

                if (i < showCount)
                {
                    // Выводим ci побайтово (little-endian, как хранится в файле)
                    for (int j = 0; j < blockSize; j++)
                    {
                        byte byt = j < ciBytes.Length ? ciBytes[j] : (byte)0;
                        sbResult.Append(byt);
                        sbResult.Append(' ');
                    }
                    if ((i + 1) % 8 == 0) sbResult.AppendLine();
                }
            }

            if (inputData.Length > 512)
                sbResult.AppendLine($"\n... (показаны первые 512 из {inputData.Length} блоков)");

            var dlg = new SaveFileDialog
            {
                Title = "Сохранить зашифрованный файл",
                FileName = Path.GetFileName(_selectedFilePath) + ".rabin",
                Filter = "Rabin encrypted (*.rabin)|*.rabin|Все файлы (*.*)|*.*",
                DefaultExt = "rabin",
                AddExtension = true
            };
            if (dlg.ShowDialog() != true) return;
            string outPath = dlg.FileName;

            byte[] header = new byte[] { (byte)blockSize };
            using (var fs = new FileStream(outPath, FileMode.Create))
            {
                fs.Write(header, 0, 1);
                fs.Write(outputData, 0, outputData.Length);
            }

            memoResult.Text = sbResult.ToString();
            lblResult.Text = "ЗАШИФРОВАННЫЙ ФАЙЛ (байты в dec)";
            txtStatus.Text = $"✅ Зашифровано → {Path.GetFileName(outPath)}  |  Ko = (n={_n}, b={_b})";
            txtInfo.Text = $"Файл сохранён: {outPath}  |  Закрытый ключ Kc = (p={_p}, q={_q})";
        }

        // ─── ДЕШИФРОВАНИЕ ФАЙЛА ───────────────────────────────────────────────────
        private void DecryptFile()
        {
            byte[] inputData = File.ReadAllBytes(_selectedFilePath);

            if (inputData.Length < 2)
                throw new Exception("Файл слишком мал или не является зашифрованным файлом Рабина.");

            int blockSize = inputData[0];
            if (blockSize < 1 || blockSize > 16)
                throw new Exception("Неверный формат файла: некорректный размер блока в заголовке.");

            int dataLen = inputData.Length - 1;
            if (dataLen % blockSize != 0)
                throw new Exception($"Файл повреждён: длина данных ({dataLen}) не кратна размеру блока ({blockSize}).");

            int blockCount = dataLen / blockSize;
            byte[] outputData = new byte[blockCount];

            var sbSource = new StringBuilder();
            var sbResult = new StringBuilder();
            int showCount = Math.Min(blockCount, 512);

            for (int i = 0; i < blockCount; i++)
            {
                byte[] block = new byte[blockSize + 1];
                Array.Copy(inputData, 1 + i * blockSize, block, 0, blockSize);
                BigInteger ci = new BigInteger(block);

                BigInteger mi = RabinDecrypt(ci, _b, _p, _q, _n);

                if (mi < 0 || mi > 255)
                    throw new Exception($"Блок {i}: не удалось расшифровать (ci={ci}). Проверьте параметры p, q, b.");

                outputData[i] = (byte)mi;

                if (i < showCount)
                {
                    // Шифртекст побайтово
                    for (int j = 0; j < blockSize; j++)
                    {
                        sbSource.Append(inputData[1 + i * blockSize + j]);
                        sbSource.Append(' ');
                    }
                    if ((i + 1) % 8 == 0) sbSource.AppendLine();

                    // Расшифрованный байт
                    sbResult.Append(mi);
                    sbResult.Append(' ');
                    if ((i + 1) % 20 == 0) sbResult.AppendLine();
                }
            }

            if (blockCount > 512)
            {
                sbSource.AppendLine($"\n... (показаны первые 512 из {blockCount} блоков)");
                sbResult.AppendLine($"\n... (показаны первые 512 из {blockCount} байт)");
            }

            memoSource.Text = sbSource.ToString();
            memoResult.Text = sbResult.ToString();

            string sourceFileName = Path.GetFileName(_selectedFilePath);
            string defaultName;
            string defaultExt;

            if (sourceFileName.EndsWith(".rabin", StringComparison.OrdinalIgnoreCase))
            {
                defaultName = sourceFileName.Substring(0, sourceFileName.Length - 6);
                defaultExt = Path.GetExtension(defaultName).TrimStart('.');
            }
            else
            {
                defaultName = sourceFileName + ".dec";
                defaultExt = "dec";
            }

            string filter = string.IsNullOrEmpty(defaultExt)
                ? "Все файлы (*.*)|*.*"
                : $"{defaultExt.ToUpper()} файлы (*.{defaultExt})|*.{defaultExt}|Все файлы (*.*)|*.*";

            var dlg = new SaveFileDialog
            {
                Title = "Сохранить расшифрованный файл",
                FileName = defaultName,
                DefaultExt = defaultExt,
                Filter = filter,
                AddExtension = true
            };
            if (dlg.ShowDialog() != true) return;
            string outPath = dlg.FileName;

            File.WriteAllBytes(outPath, outputData);
            lblResult.Text = "РАСШИФРОВАННЫЙ ФАЙЛ (байты в dec)";
            txtStatus.Text = $"✅ Расшифровано → {Path.GetFileName(outPath)}  |  Kc = (p={_p}, q={_q}, b={_b})";
            txtInfo.Text = $"Файл сохранён: {outPath}";
        }
    }
}