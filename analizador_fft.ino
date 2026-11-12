/*
 * TP 3.3 - Visualización temporal y frecuencial en plataforma de cómputo limitado
 * Matemáticas Avanzadas para Ingeniería
 *
 * Plataforma : ESP32-C6 (p. ej. ESP32-C6-DevKitC-1) - RISC-V 160 MHz, 1 núcleo, SIN FPU
 * Pantalla   : OLED SSD1306 128x64, I2C (0x3C)
 * Entrada    : teclado matricial 4x4 (escaneo directo, tarea FreeRTOS con antirrebote)
 * Señales    : 2 canales ADC1 (GPIO0 = CH0, GPIO1 = CH1), 0-3.3 V, bias a 1.65 V
 *
 * Librerías (Gestor de librerías): "Adafruit SSD1306" y "Adafruit GFX Library".
 * Placa: "ESP32C6 Dev Module". Requiere core esp32 de Espressif >= 3.0.0
 * (el C6 no existe en el core 2.x). Si usas el puerto USB nativo de la placa,
 * activa Tools > USB CDC On Boot = Enabled para ver el Serial.
 *
 * NOTA C6: sin FPU, los float se emulan por software (la FFT tarda más que en el
 * ESP32 clásico). Mide t_fft en el CSV. El ADC ADC1 del C6 solo tiene GPIO0-GPIO6.
 *
 * ---------------------------------------------------------------------------
 * RELACIÓN fs - ESCALA DE TIEMPO
 *   La pantalla muestra 128 muestras (8 divisiones x 16 px). Por eso:
 *       t/div = 16 / fs      ->      fs = 16 / (t/div)
 *   Escala nominal   Ts (us)   fs (Hz)    Ventana mostrada
 *      0.5 ms/div       32     31250       4.1 ms
 *      1   ms/div       64     15625       8.2 ms
 *      2   ms/div      128      7812      16.4 ms
 *      5   ms/div      320      3125      41.0 ms
 *   Resolución espectral: df = fs / N.   Frecuencia máxima visible: fs / 2.
 *   La fs REAL se mide en cada captura (si analogRead() es más lento que Ts,
 *   la fs real baja y df, el eje de frecuencia y la barra de estado se ajustan).
 *
 * TECLADO
 *   1,2,(3) : canal CH0, CH1, (CH2)
 *   4       : escala de tiempo   0.5 -> 1 -> 2 -> 5 ms/div
 *   5       : tamaño de FFT      128 -> 256 -> 512
 *   6       : ventana            Rect -> Hann -> Hamm -> Blck
 *   A       : RUN / HOLD
 *   B       : autoescala vertical  A(uto) / F(ija)
 *   C       : vista  TIEMPO+FFT -> solo TIEMPO -> solo FFT
 *   D       : búsqueda de pico ON/OFF (frecuencia y amplitud)
 *   *       : captura única (útil en HOLD)
 *   #       : valores por defecto
 *
 * BARRA DE ESTADO (2 líneas):
 *   CH0 RUN Hann 1ms A          canal, modo, ventana, escala, autoescala (A/F)
 *   fs15.6k N256 df61.0         fs (kHz), N, delta f (Hz)
 *
 * SALIDA SERIAL (115200 bps, CSV) para el reporte: fps, latencia, tiempos, RAM.
 * ---------------------------------------------------------------------------
 */

#include <Arduino.h>
#include <Wire.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <math.h>

// ============================== PINES ======================================
#define PIN_SDA 6
#define PIN_SCL 7

static const uint8_t ADC_PINS[] = {0, 1};            // CH0, CH1 (ADC1_CH0, ADC1_CH1)
static const uint8_t NUM_CH = sizeof(ADC_PINS) / sizeof(ADC_PINS[0]);

static const uint8_t ROW_PINS[4] = {18, 19, 20, 21}; // filas  (salidas)
static const uint8_t COL_PINS[4] = {22, 23, 10, 11}; // columnas (entradas, pull-up)
static const char KEYMAP[4][4] = {
  {'1', '2', '3', 'A'},
  {'4', '5', '6', 'B'},
  {'7', '8', '9', 'C'},
  {'*', '0', '#', 'D'}
};

// ============================== PANTALLA ===================================
#define SCREEN_W  128
#define SCREEN_H   64
#define OLED_ADDR 0x3C
// I2C a 800 kHz (si la pantalla muestra basura, bajar a 400000UL)
Adafruit_SSD1306 oled(SCREEN_W, SCREEN_H, &Wire, -1, 800000UL, 800000UL);

// Distribución vertical: [0..15] barra de estado, [18..63] área de gráficas
#define AREA_Y 18
#define AREA_H 46

// ============================== PARÁMETROS =================================
static const uint8_t  NUM_TS = 4;
static const uint32_t TS_US[NUM_TS]     = {32, 64, 128, 320};   // periodo de muestreo
static const char*    TS_NAME[NUM_TS]   = {"0.5", "1", "2", "5"};
static const uint16_t N_LIST[3]         = {128, 256, 512};
static const char*    WIN_NAME[4]       = {"Rect", "Hann", "Hamm", "Blck"};

static const uint16_t N_MAX       = 512;
static const uint16_t TRIG_EXTRA  = 64;     // muestras extra para buscar disparo
static const float    ADC_LSB     = 3.3f / 4095.0f;
static const float    PEAK_MIN_V  = 0.03f;  // por debajo se considera "sin señal"
static const uint8_t  LOG_EVERY   = 5;      // imprimir 1 de cada N cuadros

// ============================== BUFFERS ====================================
static uint16_t raw[N_MAX + TRIG_EXTRA];    // muestras crudas del ADC
static float re[N_MAX], im[N_MAX];          // FFT (re[] contiene |X| tras process())
static float win[N_MAX];                    // coeficientes de ventana
static float cosT[N_MAX / 2], sinT[N_MAX / 2]; // tabla de twiddles

// ============================== ESTADO =====================================
static uint8_t  chIdx = 0, tsIdx = 1, nIdx = 1, winIdx = 1, viewMode = 0;
static bool     running = true, autoScale = true, peakOn = true;
static volatile bool needAcq = true, needRedraw = true;
static uint16_t N = 256, trigIdx = 0;
static float    fsReal = 0, dF = 0, cg = 1.0f, magMax = 0;
static float    peakF = 0, peakA = 0;
static uint16_t peakK = 0;
static bool     peakValid = false;
static float    fps = 0;
static uint32_t tAcqUs = 0, tFftUs = 0, tDrawUs = 0, tTotUs = 0;

static QueueHandle_t keyQ;

// ============================== TECLADO ====================================
static char scanKeypad() {
  char key = 0;
  for (uint8_t r = 0; r < 4; r++) {
    digitalWrite(ROW_PINS[r], LOW);
    delayMicroseconds(10);
    for (uint8_t c = 0; c < 4; c++)
      if (!digitalRead(COL_PINS[c])) key = KEYMAP[r][c];
    digitalWrite(ROW_PINS[r], HIGH);
  }
  return key;
}

// Tarea FreeRTOS (el C6 tiene un solo núcleo): escanea cada 10 ms con antirrebote (3 lecturas iguales)
static void keypadTask(void *) {
  char last = 0, cand = 0;
  uint8_t cnt = 0;
  for (;;) {
    char k = scanKeypad();
    if (k == cand) { if (cnt < 255) cnt++; }
    else           { cand = k; cnt = 0; }
    if (cnt == 2 && cand != last) {
      last = cand;
      if (cand) xQueueSend(keyQ, &cand, 0);
    }
    vTaskDelay(pdMS_TO_TICKS(10));
  }
}

// ============================== FFT ========================================
static void initTwiddles() {
  for (uint16_t k = 0; k < N_MAX / 2; k++) {
    float a = 2.0f * PI * k / N_MAX;
    cosT[k] = cosf(a);
    sinT[k] = sinf(a);
  }
}

// FFT radix-2 decimación en tiempo, in-place, n potencia de 2 (<= N_MAX)
static void fft(float *xr, float *xi, uint16_t n) {
  // reordenamiento por inversión de bits
  for (uint16_t i = 1, j = 0; i < n; i++) {
    uint16_t bit = n >> 1;
    for (; j & bit; bit >>= 1) j ^= bit;
    j ^= bit;
    if (i < j) {
      float t = xr[i]; xr[i] = xr[j]; xr[j] = t;
      t = xi[i]; xi[i] = xi[j]; xi[j] = t;
    }
  }
  // mariposas
  for (uint16_t len = 2; len <= n; len <<= 1) {
    uint16_t half = len >> 1, step = N_MAX / len;
    for (uint16_t i = 0; i < n; i += len) {
      for (uint16_t k = 0; k < half; k++) {
        float wr = cosT[k * step], wi = -sinT[k * step];   // W = e^{-j2pi k/len}
        uint16_t a = i + k, b = a + half;
        float tr = xr[b] * wr - xi[b] * wi;
        float ti = xr[b] * wi + xi[b] * wr;
        xr[b] = xr[a] - tr;  xi[b] = xi[a] - ti;
        xr[a] += tr;         xi[a] += ti;
      }
    }
  }
}

static void buildWindow() {
  float sum = 0;
  for (uint16_t i = 0; i < N; i++) {
    float x = 2.0f * PI * i / (N - 1), w;
    switch (winIdx) {
      case 0:  w = 1.0f; break;                                              // rectangular
      case 1:  w = 0.5f - 0.5f * cosf(x); break;                             // Hann
      case 2:  w = 0.54f - 0.46f * cosf(x); break;                           // Hamming
      default: w = 0.42f - 0.5f * cosf(x) + 0.08f * cosf(2.0f * x); break;   // Blackman
    }
    win[i] = w;
    sum += w;
  }
  cg = sum / N;   // ganancia coherente (para corregir amplitud de picos)
}

// ============================== ADQUISICIÓN ================================
static void acquire() {
  const uint8_t  pin  = ADC_PINS[chIdx];
  const uint32_t Ts   = TS_US[tsIdx];
  const uint16_t ncap = N + TRIG_EXTRA;
  uint32_t t0 = micros(), next = t0, tl = t0;
  for (uint16_t i = 0; i < ncap; i++) {
    while ((int32_t)(micros() - next) < 0) { }   // espera activa hasta la siguiente muestra
    tl = micros();
    raw[i] = analogRead(pin);
    next += Ts;
  }
  // fs real: (ncap-1) intervalos entre la primera y la última muestra
  fsReal = (ncap - 1) * 1e6f / (float)(tl - t0);
  dF = fsReal / N;
}

// ============================== PROCESAMIENTO ==============================
static void process() {
  // media (componente DC) y disparo en flanco ascendente sobre la media
  float mean = 0;
  for (uint16_t i = 0; i < N; i++) mean += raw[i];
  mean /= N;

  trigIdx = 0;
  for (uint16_t i = 1; i < TRIG_EXTRA; i++) {
    if (raw[i - 1] < mean && raw[i] >= mean) { trigIdx = i; break; }
  }

  // quitar DC, aplicar ventana, FFT
  for (uint16_t i = 0; i < N; i++) {
    re[i] = (raw[i] - mean) * ADC_LSB * win[i];
    im[i] = 0;
  }
  fft(re, im, N);

  // |X| escalado a amplitud pico (V) de una senoidal: 2|X| / (N * ganancia coherente)
  const uint16_t nb = N / 2;
  const float sc = 2.0f / (N * cg);
  re[0] = 0;
  magMax = 0;
  uint16_t kp = 1;
  for (uint16_t k = 1; k < nb; k++) {
    re[k] = sqrtf(re[k] * re[k] + im[k] * im[k]) * sc;
    if (re[k] > magMax) { magMax = re[k]; kp = k; }
  }

  // búsqueda de pico con interpolación parabólica
  peakValid = false;
  if (magMax > PEAK_MIN_V && kp >= 1 && kp < nb - 1) {
    float a = re[kp - 1], b = re[kp], c = re[kp + 1];
    float den = a - 2.0f * b + c;
    float d = (fabsf(den) > 1e-9f) ? 0.5f * (a - c) / den : 0.0f;
    if (d > 0.5f) d = 0.5f;
    if (d < -0.5f) d = -0.5f;
    peakF = (kp + d) * dF;
    peakA = b - 0.25f * (a - c) * d;
    peakK = kp;
    peakValid = true;
  }
}

// ============================== DIBUJO =====================================
static void drawStatus() {
  char b[28];
  oled.setTextSize(1);
  oled.setTextColor(SSD1306_WHITE);
  snprintf(b, sizeof b, "CH%d %s %s %sms %c", chIdx, running ? "RUN" : "HLD",
           WIN_NAME[winIdx], TS_NAME[tsIdx], autoScale ? 'A' : 'F');
  oled.setCursor(0, 0);
  oled.print(b);
  snprintf(b, sizeof b, "fs%.1fk N%d df%.1f", fsReal / 1000.0f, N, dF);
  oled.setCursor(0, 8);
  oled.print(b);
  oled.drawFastHLine(0, 16, SCREEN_W, SSD1306_WHITE);
}

static void drawTime(int y0, int h) {
  const uint16_t *s = &raw[trigIdx];
  int mn = 0, mx = 4095;
  if (autoScale) {
    mn = 4095; mx = 0;
    for (uint8_t i = 0; i < SCREEN_W; i++) {
      if (s[i] < mn) mn = s[i];
      if (s[i] > mx) mx = s[i];
    }
    if (mx - mn < 64) {                // evitar ampliar ruido en exceso
      int c = (mx + mn) / 2;
      mn = (c > 32) ? c - 32 : 0;
      mx = mn + 64;
    }
  }
  float k = (h - 1) / (float)(mx - mn);

  // retícula: línea central punteada y marcas cada división (16 px)
  for (uint8_t x = 0; x < SCREEN_W; x += 4) oled.drawPixel(x, y0 + h / 2, SSD1306_WHITE);
  for (uint8_t x = 0; x < SCREEN_W; x += 16) {
    oled.drawPixel(x, y0, SSD1306_WHITE);
    oled.drawPixel(x, y0 + h - 1, SSD1306_WHITE);
  }

  int py = 0;
  for (uint8_t x = 0; x < SCREEN_W; x++) {
    int v = s[x];
    if (v < mn) v = mn;
    if (v > mx) v = mx;
    int y = y0 + h - 1 - (int)((v - mn) * k + 0.5f);
    if (x > 0) oled.drawLine(x - 1, py, x, y, SSD1306_WHITE);
    py = y;
  }
}

// Eje X: 0 ... fs/2 repartido en 128 px. Eje Y: |X| lineal (V pico).
static void drawSpec(int y0, int h) {
  const uint16_t nb = N / 2;
  float smax = autoScale ? (magMax * 1.1f > 0.05f ? magMax * 1.1f : 0.05f) : 1.65f;

  for (uint8_t x = 0; x < SCREEN_W; x++) {
    uint16_t b0 = (uint16_t)x * nb / SCREEN_W;
    uint16_t b1 = (uint16_t)(x + 1) * nb / SCREEN_W;
    if (b1 <= b0) b1 = b0 + 1;
    float m = 0;
    for (uint16_t b = b0; b < b1; b++) if (re[b] > m) m = re[b];
    int hh = (int)(m / smax * (h - 1) + 0.5f);
    if (hh > h - 1) hh = h - 1;
    if (hh > 0) oled.drawFastVLine(x, y0 + h - hh, hh, SSD1306_WHITE);
  }
  oled.drawFastHLine(0, y0 + h - 1, SCREEN_W, SSD1306_WHITE);

  if (peakOn) {
    char b[24];
    if (!peakValid)              snprintf(b, sizeof b, "---");
    else if (peakF >= 1000.0f)   snprintf(b, sizeof b, "%.2fkHz %.2fV", peakF / 1000.0f, peakA);
    else                         snprintf(b, sizeof b, "%.0fHz %.2fV", peakF, peakA);
    int w = 6 * strlen(b);
    oled.fillRect(SCREEN_W - w - 1, y0, w + 1, 8, SSD1306_BLACK);
    oled.setCursor(SCREEN_W - w, y0);
    oled.print(b);
    if (peakValid) {                    // marcador sobre el pico
      int px = (int)peakK * SCREEN_W / nb;
      oled.drawFastVLine(px, y0, 3, SSD1306_WHITE);
    }
  }
}

static void draw() {
  oled.clearDisplay();
  drawStatus();
  switch (viewMode) {
    case 0:   // TIEMPO + FFT
      drawTime(AREA_Y, 22);
      oled.drawFastHLine(0, 40, SCREEN_W, SSD1306_WHITE);
      drawSpec(42, 22);
      break;
    case 1:   // solo TIEMPO
      drawTime(AREA_Y, AREA_H);
      break;
    default:  // solo FFT
      drawSpec(AREA_Y, AREA_H);
      break;
  }
  oled.display();
}

// ============================== TECLAS =====================================
static void resetDefaults() {
  chIdx = 0; tsIdx = 1; nIdx = 1; winIdx = 1; viewMode = 0;
  running = true; autoScale = true; peakOn = true;
  N = N_LIST[nIdx];
  buildWindow();
  needAcq = true;
}

static void handleKey(char k) {
  switch (k) {
    case '1': case '2': case '3': {
      uint8_t c = k - '1';
      if (c < NUM_CH) { chIdx = c; needAcq = true; }
      break;
    }
    case '4': tsIdx = (tsIdx + 1) % NUM_TS; needAcq = true; break;
    case '5': nIdx = (nIdx + 1) % 3; N = N_LIST[nIdx]; buildWindow(); needAcq = true; break;
    case '6': winIdx = (winIdx + 1) % 4; buildWindow(); needRedraw = true; break;
    case 'A': running = !running; needRedraw = true; break;
    case 'B': autoScale = !autoScale; needRedraw = true; break;
    case 'C': viewMode = (viewMode + 1) % 3; needRedraw = true; break;
    case 'D': peakOn = !peakOn; needRedraw = true; break;
    case '*': needAcq = true; break;
    case '#': resetDefaults(); break;
    default: break;
  }
}

// ============================== SETUP / LOOP ===============================
void setup() {
  Serial.begin(115200);

  analogReadResolution(12);
  for (uint8_t i = 0; i < NUM_CH; i++) {
    pinMode(ADC_PINS[i], INPUT);
    analogSetPinAttenuation(ADC_PINS[i], ADC_11db);   // rango ~0-3.3 V
  }

  for (uint8_t r = 0; r < 4; r++) { pinMode(ROW_PINS[r], OUTPUT); digitalWrite(ROW_PINS[r], HIGH); }
  for (uint8_t c = 0; c < 4; c++) pinMode(COL_PINS[c], INPUT_PULLUP);

  Wire.begin(PIN_SDA, PIN_SCL);
  if (!oled.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR)) {
    Serial.println("ERROR: SSD1306 no encontrada (revisar SDA/SCL/direccion)");
    for (;;) delay(1000);
  }
  oled.setTextWrap(false);
  oled.clearDisplay();
  oled.display();

  initTwiddles();
  N = N_LIST[nIdx];
  buildWindow();

  keyQ = xQueueCreate(8, sizeof(char));
  xTaskCreate(keypadTask, "keypad", 2048, NULL, 1, NULL);

  Serial.printf("# Heap total=%u B, libre=%u B (RAM estatica: ver reporte de compilacion)\n",
                ESP.getHeapSize(), ESP.getFreeHeap());
  Serial.println("t_ms,canal,fs_Hz,N,df_Hz,pico_Hz,pico_V,fps,t_adq_ms,t_fft_ms,t_pant_ms,latencia_ms,heap_usado_pct");
}

void loop() {
  // 1) atender teclas
  char k;
  while (xQueueReceive(keyQ, &k, 0) == pdTRUE) handleKey(k);

  // 2) ¿hay algo que hacer?
  bool acq = running || needAcq;
  if (!acq && !needRedraw) { delay(5); return; }

  static uint32_t lastStart = 0;
  static uint8_t  logCnt = 0;
  uint32_t t0 = micros();

  if (running && lastStart && (t0 - lastStart) < 1000000UL) {
    float inst = 1e6f / (float)(t0 - lastStart);
    fps = (fps == 0) ? inst : 0.8f * fps + 0.2f * inst;
  }
  lastStart = t0;

  needAcq = false;
  needRedraw = false;

  if (acq) acquire();
  uint32_t t1 = micros();
  process();
  uint32_t t2 = micros();
  draw();
  uint32_t t3 = micros();

  tAcqUs = t1 - t0; tFftUs = t2 - t1; tDrawUs = t3 - t2; tTotUs = t3 - t0;

  // 3) registro por Serial (CSV)
  if (running && ++logCnt >= LOG_EVERY) {
    logCnt = 0;
    float heapPct = 100.0f * (1.0f - (float)ESP.getFreeHeap() / (float)ESP.getHeapSize());
    Serial.printf("%lu,%d,%.1f,%d,%.2f,%.2f,%.3f,%.1f,%.1f,%.2f,%.1f,%.1f,%.1f\n",
                  millis(), chIdx, fsReal, N, dF,
                  peakValid ? peakF : 0.0f, peakValid ? peakA : 0.0f,
                  fps, tAcqUs / 1000.0f, tFftUs / 1000.0f, tDrawUs / 1000.0f,
                  tTotUs / 1000.0f, heapPct);
  }
}
