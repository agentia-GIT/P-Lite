/*
 * Lecteur A/V - C natif Win32 + libmpv (chargée dynamiquement)
 * Compilation : voir build.sh  (mingw-w64, x86_64)
 */
#define UNICODE
#define _UNICODE
#define WIN32_LEAN_AND_MEAN
#define WINVER 0x0A00
#define _WIN32_WINNT 0x0A00
#include <windows.h>
#include <windowsx.h>
#include <commdlg.h>
#include <shellapi.h>
#include <commctrl.h>
#include <urlmon.h>
#include <wininet.h>
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#define COBJMACROS
#include <objbase.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <shlobj.h>

#define MYFILE L"mes_chaines.m3u"

/* ---------- API libmpv minimale ---------- */
typedef struct mpv_handle mpv_handle;
typedef struct { int event_id; int error; uint64_t reply_userdata; void *data; } mpv_event;
typedef struct { int num_args; const char **args; } mpv_event_client_message;
enum { MPV_FMT_STRING = 1, MPV_FMT_FLAG = 3, MPV_FMT_DOUBLE = 5 };
enum { EV_SHUTDOWN = 1, EV_FILE_LOADED = 8, EV_CLIENT_MSG = 16 };

static mpv_handle *(*p_create)(void);
static int (*p_initialize)(mpv_handle *);
static int (*p_set_option_string)(mpv_handle *, const char *, const char *);
static int (*p_command)(mpv_handle *, const char **);
static int (*p_get_property)(mpv_handle *, const char *, int, void *);
static char *(*p_get_property_string)(mpv_handle *, const char *);
static int (*p_set_property_string)(mpv_handle *, const char *, const char *);
static mpv_event *(*p_wait_event)(mpv_handle *, double);
static void (*p_free)(void *);
static void (*p_terminate_destroy)(mpv_handle *);

/* ---------- état ---------- */
static HMODULE gDll; static wchar_t gDllPath[MAX_PATH];
#define WM_LAV_LOADED (WM_APP + 1)
#define WM_LAV_FS     (WM_APP + 2)
#define WM_LAV_ESC    (WM_APP + 3)
#define WM_LAV_TRACKS (WM_APP + 4)
#define WM_LAV_OPEN   (WM_APP + 5)
#define WM_LAV_NEWVER (WM_APP + 30)

#define C_BG    RGB(13, 15, 18)
#define C_BAR   RGB(22, 25, 30)
#define C_FG    RGB(201, 209, 217)
#define C_DIM   RGB(107, 116, 128)
#define C_ACC   RGB(78, 201, 176)
#define C_TROU  RGB(42, 47, 55)
#define C_HOT   RGB(36, 41, 48)
#define C_RED   RGB(224, 84, 84)

static HINSTANCE hInst;
static HWND hMain, hVideo, hPanel, hPanelFs, hMgr, dlgOwner;
static HWND owner_w(void) { return hMgr ? hMgr : hMain; }
static wchar_t dlgPreName[256], dlgPreUrl[1100]; static int dlgNameRO;
static wchar_t chanTitle[256], selCat[96], selLang[48], selList[MAX_PATH];
static mpv_handle *mpv;
static HANDLE hThread;
static int dpi = 96;
static HFONT fUI, fMono, fSmall;
static int fullscreen = 0, tracksVisible = 1, barsShown = 1, menuOpen = 0, playing = 0;
static WINDOWPLACEMENT wpPrev = { sizeof(WINDOWPLACEMENT) };
static double gPos = -1, gDur = -1, gVol = 100;
static int gPause = 0, gMute = 0;
static int dragSeek = 0, dragVol = 0, hover = 0;
static double seekFrac = 0;
static POINT lastPt; static DWORD lastMove;
static volatile int capRunning;
static HWND hViz; static int vizOn;
static void viz_update(int realVideo);

typedef struct { int id; wchar_t label[256]; int selected; } Trk;
static Trk aud[64], sub[64];
static int nAud, nSub, lastCount = -1;

static RECT rGear, rCam, rIptv, rIptvCfg, rLang, rCat, rChan, rSeek, rVol, rOpen, rPlay, rStop, rFs, rTog, rAud, rSub, rTime;
enum { H_NONE, H_SEEK, H_VOL, H_OPEN, H_PLAY, H_STOP, H_FS, H_TOG, H_AUD, H_SUB, H_GEAR, H_CAM, H_IPTV, H_IPTVCFG, H_LANG, H_CAT, H_CHAN };

static void inval(void);
static void iptv_menu(void), iptv_cfg_menu(void), lang_menu(void), cat_menu(void), chan_menu(void), manage_window(void), settings_window(void);
static HWND cur_panel(void);
static void capture_open(void), cap_shutdown(void);
static int S(int x) { return MulDiv(x, dpi, 96); }

/* ---------- utilitaires ---------- */
static void inval(void) { InvalidateRect(hPanel, NULL, FALSE); if (hPanelFs) InvalidateRect(hPanelFs, NULL, FALSE); }
static HWND cur_panel(void) { return fullscreen ? hPanelFs : hPanel; }
static void u8w(const char *s, wchar_t *o, int n) { if (!MultiByteToWideChar(CP_UTF8, 0, s, -1, o, n)) o[0] = 0; }
static void w8(const wchar_t *s, char *o, int n) { if (!WideCharToMultiByte(CP_UTF8, 0, s, -1, o, n, NULL, NULL)) o[0] = 0; }

static void cmd(const char *a, const char *b, const char *c, const char *d) {
    const char *v[6] = { a, b, c, d, NULL, NULL };
    p_command(mpv, v);
}

static void load_file(const wchar_t *path) {
    char u[2048]; w8(path, u, sizeof u); chanTitle[0] = 0;
    cmd("loadfile", u, "replace", NULL);
    p_set_property_string(mpv, "pause", "no");
}

static int tprop(int i, const char *k, char *out, int n) {
    char name[96]; snprintf(name, sizeof name, "track-list/%d/%s", i, k);
    char *s = p_get_property_string(mpv, name);
    if (!s) { out[0] = 0; return 0; }
    strncpy(out, s, n - 1); out[n - 1] = 0; p_free(s); return 1;
}

static void app(wchar_t *d, const wchar_t *s) {
    size_t l = wcslen(d);
    if (l && l < 250) wcscat(d, L"  ·  ");
    wcsncat(d, s, 255 - wcslen(d));
}

static void refresh_tracks(void) {
    nAud = nSub = 0;
    char b[512];
    if (!tprop(0, "id", b, sizeof b) && 0) {}
    char *cs = p_get_property_string(mpv, "track-list/count");
    int cnt = cs ? atoi(cs) : 0; if (cs) p_free(cs);
    lastCount = cnt; int realVideo = 0;
    for (int i = 0; i < cnt; i++) {
        char type[16], id[16], lang[64], title[256], codec[32], ch[16], selc[8];
        tprop(i, "type", type, sizeof type);
        int isA = !strcmp(type, "audio"), isS = !strcmp(type, "sub");
        if (!strcmp(type, "video")) { char al[8]; tprop(i, "albumart", al, sizeof al); if (strcmp(al, "yes")) realVideo = 1; }
        if (!isA && !isS) continue;
        tprop(i, "id", id, sizeof id); tprop(i, "lang", lang, sizeof lang);
        tprop(i, "title", title, sizeof title); tprop(i, "codec", codec, sizeof codec);
        tprop(i, "demux-channel-count", ch, sizeof ch); tprop(i, "selected", selc, sizeof selc);
        Trk t; memset(&t, 0, sizeof t);
        t.id = atoi(id); t.selected = !strcmp(selc, "yes");
        wchar_t w[256], lab[256]; _snwprintf(lab, 255, L"#%d", t.id); lab[255] = 0;
        if (lang[0]) { u8w(lang, w, 256); app(lab, w); }
        if (title[0]) { u8w(title, w, 256); app(lab, w); }
        if (codec[0]) { u8w(codec, w, 256); CharUpperW(w); app(lab, w); }
        if (isA && ch[0]) {
            int c = atoi(ch);
            const wchar_t *s = c == 1 ? L"mono" : c == 2 ? L"2.0" : c == 6 ? L"5.1" : c == 8 ? L"7.1" : NULL;
            if (s) app(lab, s); else { _snwprintf(w, 255, L"%dch", c); w[255] = 0; app(lab, w); }
        }
        wcsncpy(t.label, lab, 255);
        if (isA && nAud < 64) aud[nAud++] = t;
        if (isS && nSub < 64) sub[nSub++] = t;
    }
    viz_update(realVideo);
    inval();
}

/* ---------- mise en page ---------- */
static int panel_height(void) { return (tracksVisible ? S(34) : 0) + S(64); }

static void place_viz(int w, int h) { if (hViz) SetWindowPos(hViz, HWND_TOP, 0, 0, w, h, SWP_NOACTIVATE | (vizOn ? SWP_SHOWWINDOW : SWP_HIDEWINDOW)); }
static void do_layout(void) {
    RECT rc; GetClientRect(hMain, &rc);
    int w = rc.right, h = rc.bottom, ph = panel_height(); if (ph > h) ph = h;
    if (fullscreen) {                         /* mode TV : la vidéo occupe tout l'écran */
        ShowWindow(hPanel, SW_HIDE);
        SetWindowPos(hVideo, NULL, 0, 0, w, h, SWP_NOZORDER); place_viz(w, h);
        if (barsShown) {
            POINT p = { 0, h - ph }; ClientToScreen(hMain, &p);
            SetWindowPos(hPanelFs, HWND_TOPMOST, p.x, p.y, w, ph, SWP_NOACTIVATE | SWP_SHOWWINDOW);
        } else ShowWindow(hPanelFs, SW_HIDE);
    } else {
        if (hPanelFs) ShowWindow(hPanelFs, SW_HIDE);
        SetWindowPos(hVideo, NULL, 0, 0, w, h - ph, SWP_NOZORDER); place_viz(w, h - ph);
        SetWindowPos(hPanel, NULL, 0, h - ph, w, ph, SWP_NOZORDER | SWP_SHOWWINDOW);
    }
}

static void calc_rects(int w) {
    int th = tracksVisible ? S(34) : 0, y0 = th, by = y0 + S(26), bs = S(34);
    SetRect(&rAud, S(10), S(5), w / 2 - S(6), S(29));
    SetRect(&rSub, w / 2 + S(6), S(5), w - S(10), S(29));
    SetRect(&rSeek, S(12), y0 + S(6), w - S(12), y0 + S(22));
    SetRect(&rOpen, S(6), by, S(6) + bs, by + bs);
    SetRect(&rPlay, rOpen.right + S(2), by, rOpen.right + S(2) + bs, by + bs);
    SetRect(&rStop, rPlay.right + S(2), by, rPlay.right + S(2) + bs, by + bs);
    SetRect(&rTime, rStop.right + S(12), by, rStop.right + S(142), by + bs);
    SetRect(&rTog, w - S(6) - bs, by, w - S(6), by + bs);
    SetRect(&rFs, rTog.left - S(2) - bs, by, rTog.left - S(2), by + bs);
    SetRect(&rVol, rFs.left - S(16) - S(100), by + S(10), rFs.left - S(16), by + bs - S(10));
    {   /* IPTV [fleche] [categorie] [chaine] : centre entre le temps et le volume */
        SetRect(&rGear, rTime.right + S(2), by, rTime.right + S(2) + bs, by + bs);
        SetRect(&rCam, rGear.right + S(2), by, rGear.right + S(2) + bs, by + bs);
        int gl = rCam.right + S(6), gr = rVol.left - S(48), bw = S(104), cfg = S(22);
        int avail = gr - gl, cw = (avail - bw - cfg - S(20)) / 3;
        if (cw > S(190)) cw = S(190); if (cw < S(60)) cw = S(60);
        int total = bw + cfg + S(8) + cw * 3 + S(12), x = gl + (avail - total) / 2; if (x < gl) x = gl;
        SetRect(&rIptv, x, by, x + bw, by + bs);
        SetRect(&rIptvCfg, rIptv.right, by, rIptv.right + cfg, by + bs);
        SetRect(&rLang, rIptvCfg.right + S(8), by + S(5), rIptvCfg.right + S(8) + cw, by + bs - S(5));
        SetRect(&rCat, rLang.right + S(6), by + S(5), rLang.right + S(6) + cw, by + bs - S(5));
        SetRect(&rChan, rCat.right + S(6), by + S(5), rCat.right + S(6) + cw, by + bs - S(5));
    }
}

/* ---------- dessin ---------- */
static void fill(HDC dc, const RECT *r, COLORREF c) {
    SetDCBrushColor(dc, c); FillRect(dc, r, (HBRUSH)GetStockObject(DC_BRUSH));
}
static void frect(HDC dc, int l, int t, int r, int b, COLORREF c) { RECT x = { l, t, r, b }; fill(dc, &x, c); }
static void poly(HDC dc, POINT *p, int n, COLORREF c) {
    SetDCBrushColor(dc, c); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN));
    Polygon(dc, p, n);
}
static void text(HDC dc, const wchar_t *s, RECT *r, COLORREF c, HFONT f, UINT fl) {
    SetBkMode(dc, TRANSPARENT); SetTextColor(dc, c); SelectObject(dc, f);
    DrawTextW(dc, s, -1, r, fl | DT_SINGLELINE | DT_VCENTER | DT_NOPREFIX);
}
static void fmt_time(double t, wchar_t *o) {
    if (t < 0) { wcscpy(o, L"--:--"); return; }
    int s = (int)t, h = s / 3600, m = (s % 3600) / 60; s %= 60;
    if (h) _snwprintf(o, 31, L"%d:%02d:%02d", h, m, s); else _snwprintf(o, 31, L"%02d:%02d", m, s);
}
static void bar(HDC dc, RECT *r, double f, COLORREF fillc, int th, int knob) {
    int cy = (r->top + r->bottom) / 2;
    frect(dc, r->left, cy - th / 2, r->right, cy - th / 2 + th, C_TROU);
    int x = r->left + (int)((r->right - r->left) * f);
    frect(dc, r->left, cy - th / 2, x, cy - th / 2 + th, fillc);
    SetDCBrushColor(dc, C_FG); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN));
    Ellipse(dc, x - knob, cy - knob, x + knob, cy + knob);
}
static void hoverbg(HDC dc, RECT *r, int id) { if (hover == id) fill(dc, r, C_HOT); }

static void chip(HDC dc, RECT *r, const wchar_t *name, int nameW, const wchar_t *val, int id) {
    fill(dc, r, hover == id ? C_TROU : C_HOT);
    RECT t = *r; t.left += S(8); text(dc, name, &t, C_DIM, fSmall, DT_LEFT);
    t = *r; t.left += S(8) + nameW; t.right -= S(22); text(dc, val, &t, C_FG, fUI, DT_LEFT | DT_END_ELLIPSIS);
    int cx = r->right - S(12), cy = (r->top + r->bottom) / 2;
    POINT p[3] = { { cx - S(4), cy - S(2) }, { cx + S(4), cy - S(2) }, { cx, cy + S(3) } }; poly(dc, p, 3, C_ACC);
}

static void chip2(HDC dc, RECT *r, const wchar_t *t, int dim, int id) {
    fill(dc, r, hover == id ? C_TROU : C_HOT);
    RECT x = *r; x.left += S(8); x.right -= S(22); text(dc, t, &x, dim ? C_DIM : C_FG, fUI, DT_LEFT | DT_END_ELLIPSIS);
    int cx = r->right - S(12), cy = (r->top + r->bottom) / 2;
    POINT p[3] = { { cx - S(4), cy - S(2) }, { cx + S(4), cy - S(2) }, { cx, cy + S(3) } }; poly(dc, p, 3, C_ACC);
}

static void paint_panel(HDC dc, int w, int h) {
    RECT all = { 0, 0, w, h }; fill(dc, &all, C_BAR);
    calc_rects(w);
    if (tracksVisible) {
        RECT sep = { 0, S(33), w, S(34) }; fill(dc, &sep, C_BG);
        const wchar_t *a = L"—", *s = L"Désactivés";
        for (int i = 0; i < nAud; i++) if (aud[i].selected) a = aud[i].label;
        for (int i = 0; i < nSub; i++) if (sub[i].selected) s = sub[i].label;
        chip(dc, &rAud, L"AUDIO", S(52), a, H_AUD);
        chip(dc, &rSub, L"SOUS-TITRES", S(86), s, H_SUB);
    }
    /* seek */
    double f = dragSeek ? seekFrac : (gDur > 0 && gPos >= 0 ? gPos / gDur : 0);
    if (f < 0) f = 0; if (f > 1) f = 1;
    bar(dc, &rSeek, f, C_ACC, S(3), S(6));
    /* boutons */
    hoverbg(dc, &rOpen, H_OPEN); hoverbg(dc, &rPlay, H_PLAY); hoverbg(dc, &rStop, H_STOP);
    hoverbg(dc, &rFs, H_FS); hoverbg(dc, &rTog, H_TOG);
    int cx = (rOpen.left + rOpen.right) / 2, cy = (rOpen.top + rOpen.bottom) / 2;
    POINT e[3] = { { cx, cy - S(7) }, { cx - S(8), cy + S(1) }, { cx + S(8), cy + S(1) } }; poly(dc, e, 3, C_FG);
    frect(dc, cx - S(8), cy + S(4), cx + S(8), cy + S(7), C_FG);
    cx = (rPlay.left + rPlay.right) / 2; cy = (rPlay.top + rPlay.bottom) / 2;
    if (gPause || !playing) { POINT p[3] = { { cx - S(4), cy - S(8) }, { cx - S(4), cy + S(8) }, { cx + S(8), cy } }; poly(dc, p, 3, C_ACC); }
    else { frect(dc, cx - S(6), cy - S(7), cx - S(2), cy + S(7), C_ACC); frect(dc, cx + S(2), cy - S(7), cx + S(6), cy + S(7), C_ACC); }
    cx = (rStop.left + rStop.right) / 2; cy = (rStop.top + rStop.bottom) / 2;
    frect(dc, cx - S(5), cy - S(5), cx + S(5), cy + S(5), C_FG);
    cx = (rFs.left + rFs.right) / 2; cy = (rFs.top + rFs.bottom) / 2;
    { int a = S(8), b = S(6), l = S(5), t = S(2);
      frect(dc, cx - a, cy - b, cx - a + l, cy - b + t, C_FG); frect(dc, cx - a, cy - b, cx - a + t, cy - b + l, C_FG);
      frect(dc, cx + a - l, cy - b, cx + a, cy - b + t, C_FG); frect(dc, cx + a - t, cy - b, cx + a, cy - b + l, C_FG);
      frect(dc, cx - a, cy + b - t, cx - a + l, cy + b, C_FG); frect(dc, cx - a, cy + b - l, cx - a + t, cy + b, C_FG);
      frect(dc, cx + a - l, cy + b - t, cx + a, cy + b, C_FG); frect(dc, cx + a - t, cy + b - l, cx + a, cy + b, C_FG); }
    cx = (rTog.left + rTog.right) / 2; cy = (rTog.top + rTog.bottom) / 2;
    if (tracksVisible) { POINT p[3] = { { cx - S(6), cy - S(3) }, { cx + S(6), cy - S(3) }, { cx, cy + S(4) } }; poly(dc, p, 3, C_FG); }
    else { POINT p[3] = { { cx - S(6), cy + S(3) }, { cx + S(6), cy + S(3) }, { cx, cy - S(4) } }; poly(dc, p, 3, C_ACC); }
    /* temps */
    wchar_t a[32], b[32], tt[80];
    double shown = dragSeek ? seekFrac * gDur : gPos;
    fmt_time(shown, a); fmt_time(gDur, b); _snwprintf(tt, 79, L"%s / %s", a, b); tt[79] = 0;
    text(dc, tt, &rTime, C_DIM, fMono, DT_LEFT);
    /* engrenage (parametres) */
    hoverbg(dc, &rGear, H_GEAR);
    { int cx = (rGear.left + rGear.right) / 2, cy = (rGear.top + rGear.bottom) / 2; POINT g[32];
      double R = S(9), r = S(6.5);
      for (int i = 0; i < 8; i++) {
          double b = i * 3.14159265 / 4;
          double a[4] = { b - 0.30, b - 0.17, b + 0.17, b + 0.30 }; double rad[4] = { r, R, R, r };
          for (int k = 0; k < 4; k++) { g[i * 4 + k].x = cx + (LONG)(rad[k] * cos(a[k])); g[i * 4 + k].y = cy + (LONG)(rad[k] * sin(a[k])); }
      }
      COLORREF gc = hover == H_GEAR ? C_ACC : C_FG; poly(dc, g, 32, gc);
      SetDCBrushColor(dc, hover == H_GEAR ? C_HOT : C_BAR); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN));
      Ellipse(dc, cx - S(3), cy - S(3), cx + S(3) + 1, cy + S(3) + 1); }
    /* camera : capture ecran */
    hoverbg(dc, &rCam, H_CAM);
    { int cx = (rCam.left + rCam.right) / 2, cy = (rCam.top + rCam.bottom) / 2; COLORREF kc = hover == H_CAM ? C_ACC : C_FG;
      frect(dc, cx - S(10), cy - S(6), cx + S(4), cy + S(7), kc);
      POINT kt[4] = { { cx + S(5), cy - S(1) }, { cx + S(11), cy - S(5) }, { cx + S(11), cy + S(6) }, { cx + S(5), cy + S(2) } }; poly(dc, kt, 4, kc);
      COLORREF dotc = capRunning ? (((GetTickCount() / 500) % 2) ? C_BAR : C_RED) : (hover == H_CAM ? C_HOT : C_BAR);
      SetDCBrushColor(dc, dotc); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN));
      Ellipse(dc, cx - S(7), cy - S(3), cx - S(1), cy + S(4)); }
    /* IPTV : bouton (chaines enregistrees) + fleche (configuration) + categorie + chaine */
    hoverbg(dc, &rIptv, H_IPTV);
    { wchar_t lb[MAX_PATH]; const wchar_t *t = L"IPTV";
      if (selList[0]) { if (!_wcsicmp(selList, MYFILE)) wcscpy(lb, L"Mes cha\u00eenes"); else { wcscpy(lb, selList); wchar_t *d = wcsrchr(lb, L'.'); if (d) *d = 0; } t = lb; }
      RECT tr = rIptv; tr.left += S(4); tr.right -= S(4); text(dc, t, &tr, selList[0] ? C_ACC : C_FG, fUI, DT_CENTER | DT_END_ELLIPSIS); }
    hoverbg(dc, &rIptvCfg, H_IPTVCFG);
    { int tx = (rIptvCfg.left + rIptvCfg.right) / 2, ty = (rIptvCfg.top + rIptvCfg.bottom) / 2;
      POINT tp[3] = { { tx - S(4), ty - S(2) }, { tx + S(4), ty - S(2) }, { tx, ty + S(3) } }; poly(dc, tp, 3, C_ACC); }
    chip2(dc, &rLang, selLang[0] ? selLang : L"Langue", !selLang[0], H_LANG);
    chip2(dc, &rCat, selCat[0] ? selCat : L"Cat\u00e9gorie", !selCat[0], H_CAT);
    chip2(dc, &rChan, chanTitle[0] ? chanTitle : L"Cha\u00eene", !chanTitle[0], H_CHAN);
    /* volume */
    RECT lv = { rVol.left - S(34), rVol.top, rVol.left - S(6), rVol.bottom };
    text(dc, L"VOL", &lv, C_DIM, fSmall, DT_RIGHT);
    bar(dc, &rVol, gVol / 130.0, gMute ? C_DIM : C_ACC, S(3), S(5));
}

static int hit(int x, int y) {
    POINT p = { x, y };
    if (tracksVisible && PtInRect(&rAud, p)) return H_AUD;
    if (tracksVisible && PtInRect(&rSub, p)) return H_SUB;
    RECT sk = rSeek; sk.top -= S(4); sk.bottom += S(4);
    if (PtInRect(&sk, p)) return H_SEEK;
    RECT v = rVol; v.top -= S(6); v.bottom += S(6);
    if (PtInRect(&v, p)) return H_VOL;
    if (PtInRect(&rOpen, p)) return H_OPEN; if (PtInRect(&rPlay, p)) return H_PLAY;
    if (PtInRect(&rStop, p)) return H_STOP; if (PtInRect(&rFs, p)) return H_FS;
    if (PtInRect(&rTog, p)) return H_TOG;
    if (PtInRect(&rGear, p)) return H_GEAR; if (PtInRect(&rCam, p)) return H_CAM; if (PtInRect(&rIptv, p)) return H_IPTV; if (PtInRect(&rIptvCfg, p)) return H_IPTVCFG;
    if (PtInRect(&rLang, p)) return H_LANG; if (PtInRect(&rCat, p)) return H_CAT; if (PtInRect(&rChan, p)) return H_CHAN;
    return H_NONE;
}

/* ---------- actions ---------- */
static void toggle_pause(void) { cmd("cycle", "pause", NULL, NULL); }
static void toggle_tracks(void) { tracksVisible = !tracksVisible; do_layout(); inval(); }

static void toggle_fs(void) {
    if (!fullscreen) {
        GetWindowPlacement(hMain, &wpPrev);
        MONITORINFO mi = { sizeof mi }; GetMonitorInfo(MonitorFromWindow(hMain, MONITOR_DEFAULTTONEAREST), &mi);
        LONG_PTR st = GetWindowLongPtr(hMain, GWL_STYLE);
        SetWindowLongPtr(hMain, GWL_STYLE, st & ~WS_OVERLAPPEDWINDOW);
        fullscreen = 1; barsShown = 0; lastMove = 0; GetCursorPos(&lastPt);
        SetWindowPos(hMain, HWND_TOP, mi.rcMonitor.left, mi.rcMonitor.top,
                     mi.rcMonitor.right - mi.rcMonitor.left, mi.rcMonitor.bottom - mi.rcMonitor.top,
                     SWP_NOOWNERZORDER | SWP_FRAMECHANGED);
    } else {
        fullscreen = 0; barsShown = 1;
        SetWindowLongPtr(hMain, GWL_STYLE, GetWindowLongPtr(hMain, GWL_STYLE) | WS_OVERLAPPEDWINDOW);
        SetWindowPlacement(hMain, &wpPrev);
        SetWindowPos(hMain, NULL, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOOWNERZORDER | SWP_FRAMECHANGED);
    }
    do_layout();
}

static void open_dialog(void) {
    wchar_t buf[4096] = L"";
    OPENFILENAMEW o; memset(&o, 0, sizeof o);
    o.lStructSize = sizeof o; o.hwndOwner = hMain; o.lpstrFile = buf; o.nMaxFile = 4096;
    o.lpstrFilter = L"Médias\0*.mkv;*.mp4;*.avi;*.mov;*.webm;*.ts;*.m2ts;*.mts;*.mpg;*.mpeg;*.vob;*.wmv;*.flv;*.m4v;*.3gp;*.ogv;"
                    L"*.ac3;*.eac3;*.dts;*.thd;*.flac;*.mp3;*.aac;*.m4a;*.ogg;*.opus;*.wav;*.wma;*.mka;*.aiff;*.ape;*.wv\0"
                    L"Tous les fichiers\0*.*\0";
    o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (GetOpenFileNameW(&o)) load_file(buf);
}

static void pick_menu(int audio) {
    HMENU m = CreatePopupMenu();
    Trk *arr = audio ? aud : sub; int n = audio ? nAud : nSub, any = 0;
    if (!audio) AppendMenuW(m, MF_STRING, 3000, L"Désactivés");
    for (int i = 0; i < n; i++) {
        wchar_t t[600]; int k = 0;
        for (const wchar_t *p = arr[i].label; *p && k < 590; p++) { t[k++] = *p; if (*p == L'&') t[k++] = L'&'; }
        t[k] = 0;
        AppendMenuW(m, MF_STRING | (arr[i].selected ? MF_CHECKED : 0), (audio ? 1000 : 2000) + i, t);
        if (arr[i].selected) any = 1;
    }
    if (!audio) CheckMenuItem(m, 3000, MF_BYCOMMAND | (any ? MF_UNCHECKED : MF_CHECKED));
    if (audio && n == 0) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune piste audio");
    RECT r = audio ? rAud : rSub; POINT p = { r.left, r.top }; ClientToScreen(cur_panel(), &p);
    menuOpen = 1;
    int c = TrackPopupMenu(m, TPM_BOTTOMALIGN | TPM_LEFTALIGN | TPM_RETURNCMD, p.x, p.y - S(2), 0, cur_panel(), NULL);
    menuOpen = 0; DestroyMenu(m);
    char v[16];
    if (c >= 1000 && c < 1100) { snprintf(v, sizeof v, "%d", aud[c - 1000].id); p_set_property_string(mpv, "aid", v); }
    else if (c >= 2000 && c < 2100) { snprintf(v, sizeof v, "%d", sub[c - 2000].id); p_set_property_string(mpv, "sid", v); }
    else if (c == 3000) p_set_property_string(mpv, "sid", "no");
    if (c) { Sleep(30); refresh_tracks(); }
    SetFocus(hMain);
}

static void set_vol_x(int x) {
    double f = (double)(x - rVol.left) / (rVol.right - rVol.left);
    if (f < 0) f = 0; if (f > 1) f = 1;
    char v[32]; snprintf(v, sizeof v, "%.0f", f * 130); gVol = f * 130; gMute = 0;
    p_set_property_string(mpv, "mute", "no"); p_set_property_string(mpv, "volume", v);
}
static void set_seek_x(int x) {
    seekFrac = (double)(x - rSeek.left) / (rSeek.right - rSeek.left);
    if (seekFrac < 0) seekFrac = 0; if (seekFrac > 1) seekFrac = 1;
}


/* ================= IPTV ================= */
static int nChans, nFiles, nCats;
static wchar_t cats[512][96];
static int nLangs;
static wchar_t langs[64][40];
static int nChansRef(void) { return nChans; }
static int migrate_playlists(void);
static void save_sel(void);
typedef struct { wchar_t name[128]; wchar_t group[96]; wchar_t lang[40]; char url[1024]; int file; } Chan;
#define MAXCH 40000
static Chan *chans; static int capChans;
static int ensure_cap(void) {
    if (nChansRef() < capChans) return 1;
    int nc = capChans ? capChans * 2 : 2048; if (nc > MAXCH) nc = MAXCH;
    if (nChansRef() >= nc) return 0;
    Chan *p = (Chan *)realloc(chans, (size_t)nc * sizeof(Chan)); if (!p) return 0;
    chans = p; capChans = nc; return 1;
}

static wchar_t fileNames[64][MAX_PATH];
static wchar_t iptvDir[MAX_PATH];

static void iptv_init_dir(void) {
    GetModuleFileNameW(NULL, iptvDir, MAX_PATH);
    wchar_t *p = wcsrchr(iptvDir, L'\\'); if (p) *p = 0;
    wcscat(iptvDir, L"\\iptv");
    CreateDirectoryW(iptvDir, NULL);
}

static char *read_all(const wchar_t *path) {
    HANDLE f = CreateFileW(path, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (f == INVALID_HANDLE_VALUE) return NULL;
    DWORD sz = GetFileSize(f, NULL), rd = 0;
    char *b = (char *)malloc(sz + 2);
    if (!b) { CloseHandle(f); return NULL; }
    ReadFile(f, b, sz, &rd, NULL); b[rd] = 0; CloseHandle(f); return b;
}


static const struct { const char *k; const wchar_t *v; } LANGN[] = {
    {"french", L"Français"}, {"fra", L"Français"}, {"fre", L"Français"}, {"fr", L"Français"},
    {"english", L"Anglais"}, {"eng", L"Anglais"}, {"en", L"Anglais"}, {"spanish", L"Espagnol"}, {"spa", L"Espagnol"}, {"es", L"Espagnol"},
    {"german", L"Allemand"}, {"deu", L"Allemand"}, {"ger", L"Allemand"}, {"de", L"Allemand"}, {"italian", L"Italien"}, {"ita", L"Italien"}, {"it", L"Italien"},
    {"portuguese", L"Portugais"}, {"por", L"Portugais"}, {"pt", L"Portugais"}, {"arabic", L"Arabe"}, {"ara", L"Arabe"}, {"ar", L"Arabe"},
    {"dutch", L"Néerlandais"}, {"nld", L"Néerlandais"}, {"nl", L"Néerlandais"}, {"russian", L"Russe"}, {"rus", L"Russe"}, {"ru", L"Russe"},
    {"turkish", L"Turc"}, {"tur", L"Turc"}, {"tr", L"Turc"}, {"polish", L"Polonais"}, {"pol", L"Polonais"}, {"chinese", L"Chinois"}, {"zho", L"Chinois"},
    {"japanese", L"Japonais"}, {"jpn", L"Japonais"}, {"korean", L"Coréen"}, {"kor", L"Coréen"}, {"hindi", L"Hindi"}, {"hin", L"Hindi"},
    {"greek", L"Grec"}, {"ell", L"Grec"}, {"romanian", L"Roumain"}, {"ron", L"Roumain"}, {"swedish", L"Suédois"}, {"ukrainian", L"Ukrainien"},
    {"hebrew", L"Hébreu"}, {"persian", L"Persan"}, {"urdu", L"Ourdou"}, {"indonesian", L"Indonésien"}, {"thai", L"Thaï"}, {"vietnamese", L"Vietnamien"},
    {"czech", L"Tchèque"}, {"hungarian", L"Hongrois"}, {"danish", L"Danois"}, {"norwegian", L"Norvégien"}, {"finnish", L"Finnois"}, {NULL, NULL} };
static const struct { const char *cc; const wchar_t *v; } CTRY[] = {
    {"fr", L"Français"}, {"us", L"Anglais"}, {"uk", L"Anglais"}, {"gb", L"Anglais"}, {"au", L"Anglais"}, {"nz", L"Anglais"}, {"ie", L"Anglais"},
    {"de", L"Allemand"}, {"at", L"Allemand"}, {"es", L"Espagnol"}, {"mx", L"Espagnol"}, {"ar", L"Espagnol"}, {"cl", L"Espagnol"}, {"co", L"Espagnol"},
    {"pe", L"Espagnol"}, {"ve", L"Espagnol"}, {"uy", L"Espagnol"}, {"it", L"Italien"}, {"pt", L"Portugais"}, {"br", L"Portugais"}, {"nl", L"Néerlandais"},
    {"ru", L"Russe"}, {"tr", L"Turc"}, {"pl", L"Polonais"}, {"ro", L"Roumain"}, {"gr", L"Grec"}, {"se", L"Suédois"}, {"no", L"Norvégien"},
    {"dk", L"Danois"}, {"fi", L"Finnois"}, {"cz", L"Tchèque"}, {"hu", L"Hongrois"}, {"ua", L"Ukrainien"}, {"jp", L"Japonais"}, {"kr", L"Coréen"},
    {"cn", L"Chinois"}, {"tw", L"Chinois"}, {"hk", L"Chinois"}, {"sa", L"Arabe"}, {"ae", L"Arabe"}, {"eg", L"Arabe"}, {"ma", L"Arabe"}, {"dz", L"Arabe"},
    {"tn", L"Arabe"}, {"iq", L"Arabe"}, {"sy", L"Arabe"}, {"lb", L"Arabe"}, {"jo", L"Arabe"}, {"kw", L"Arabe"}, {"qa", L"Arabe"}, {"il", L"Hébreu"},
    {"ir", L"Persan"}, {"pk", L"Ourdou"}, {"id", L"Indonésien"}, {"th", L"Thaï"}, {"vn", L"Vietnamien"}, {NULL, NULL} };

static void set_lang(Chan *c, const char *attr, const char *tid) {
    c->lang[0] = 0;
    if (attr[0]) {
        char a[64]; size_t i = 0; while (attr[i] && attr[i] != ';' && attr[i] != ',' && i < 63) { a[i] = (char)tolower((unsigned char)attr[i]); i++; }
        while (i && a[i - 1] == ' ') i--; a[i] = 0;
        const char *st = a; while (*st == ' ') st++;
        for (int k = 0; LANGN[k].k; k++) if (!strcmp(st, LANGN[k].k)) { wcscpy(c->lang, LANGN[k].v); return; }
        if (*st) { u8w(st, c->lang, 40); c->lang[0] = towupper(c->lang[0]); return; }
    }
    const char *d = strrchr(tid, '.');
    if (d) {
        char cc[4] = ""; int n = 0; for (d++; *d && *d != '@' && n < 3; d++) cc[n++] = (char)tolower((unsigned char)*d); cc[n] = 0;
        for (int k = 0; CTRY[k].cc; k++) if (!strcmp(cc, CTRY[k].cc)) { wcscpy(c->lang, CTRY[k].v); return; }
    }
}

static void parse_m3u(const wchar_t *path, int fileIdx) {
    char *buf = read_all(path); if (!buf) return;
    char *p = buf; if ((unsigned char)p[0] == 0xEF && (unsigned char)p[1] == 0xBB && (unsigned char)p[2] == 0xBF) p += 3;
    char name[256] = "", grp[256] = "", lng[128] = "", tid[160] = "";
    while (*p && ensure_cap()) {
        char *e = strchr(p, '\n'); size_t len = e ? (size_t)(e - p) : strlen(p);
        char line[1200]; if (len > 1199) len = 1199; memcpy(line, p, len); line[len] = 0;
        while (len && (line[len - 1] == '\r' || line[len - 1] == ' ' || line[len - 1] == '\t')) line[--len] = 0;
        p = e ? e + 1 : p + strlen(p);
        if (!len) continue;
        if (!strncmp(line, "#EXTINF", 7)) {
            grp[0] = lng[0] = tid[0] = 0;
            { char *x = strstr(line, "tvg-language=\""); if (x) { x += 14; char *q = strchr(x, '"'); if (q) { size_t l = (size_t)(q - x); if (l > 127) l = 127; memcpy(lng, x, l); lng[l] = 0; } } }
            { char *x = strstr(line, "tvg-id=\""); if (x) { x += 8; char *q = strchr(x, '"'); if (q) { size_t l = (size_t)(q - x); if (l > 159) l = 159; memcpy(tid, x, l); tid[l] = 0; } } }
            char *g = strstr(line, "group-title=\"");
            if (g) { g += 13; char *q = strchr(g, '"'); if (q) { size_t gl = (size_t)(q - g); if (gl > 255) gl = 255; memcpy(grp, g, gl); grp[gl] = 0; } }
            int inq = 0; char *c = NULL;
            for (char *q = line; *q; q++) { if (*q == '"') inq = !inq; else if (*q == ',' && !inq) { c = q; break; } }
            strncpy(name, c ? c + 1 : "", 255); name[255] = 0;
            char *q = name; while (*q == ' ') q++; memmove(name, q, strlen(q) + 1);
        } else if (line[0] != '#') {
            Chan *c = &chans[nChans++]; memset(c, 0, sizeof *c);
            strncpy(c->url, line, 1023); c->file = fileIdx;
            u8w(name[0] ? name : line, c->name, 128);
            if (grp[0]) u8w(grp, c->group, 96);
            set_lang(c, lng, tid); if (!c->lang[0]) wcscpy(c->lang, L"Non pr\u00e9cis\u00e9e");
            name[0] = 0; grp[0] = lng[0] = tid[0] = 0;
        }
    }
    free(buf);
}

static void build_cats(void);
static void load_channels_raw(void) {
    nChans = 0; nFiles = 0;
    wchar_t pat[MAX_PATH], full[MAX_PATH];
    wcscpy(fileNames[nFiles++], MYFILE);                 /* fichier personnel = index 0 */
    _snwprintf(full, MAX_PATH - 1, L"%s\\%s", iptvDir, MYFILE); full[MAX_PATH - 1] = 0;
    parse_m3u(full, 0);
    _snwprintf(pat, MAX_PATH - 1, L"%s\\*.m3u*", iptvDir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) return;
    do {
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) continue;
        if (!_wcsicmp(fd.cFileName, MYFILE) || nFiles >= 64) continue;
        wcscpy(fileNames[nFiles], fd.cFileName);
        _snwprintf(full, MAX_PATH - 1, L"%s\\%s", iptvDir, fd.cFileName); full[MAX_PATH - 1] = 0;
        parse_m3u(full, nFiles); nFiles++;
    } while (FindNextFileW(h, &fd));
    FindClose(h);
}

static int cat_cmp(const void *a, const void *b) {
    const wchar_t *x = (const wchar_t *)a, *y = (const wchar_t *)b;
    int mx = !wcscmp(x, L"Mes cha\u00eenes"), my = !wcscmp(y, L"Mes cha\u00eenes");
    if (mx != my) return mx ? -1 : 1;
    return _wcsicmp(x, y);
}
static int lang_cmp(const void *a, const void *b) {
    const wchar_t *x = (const wchar_t *)a, *y = (const wchar_t *)b;
    int mx = !wcscmp(x, L"Non pr\u00e9cis\u00e9e"), my = !wcscmp(y, L"Non pr\u00e9cis\u00e9e");
    if (mx != my) return mx ? 1 : -1;
    return _wcsicmp(x, y);
}
static int in_list(int i) { return !selList[0] || (chans[i].file >= 0 && chans[i].file < nFiles && !_wcsicmp(fileNames[chans[i].file], selList)); }
static int in_lang(int i) { return in_list(i) && (!selLang[0] || !wcscmp(chans[i].lang, selLang)); }
static void build_cats(void) {
    nCats = 0; nLangs = 0;
    for (int i = 0; i < nChans; i++) {
        if (!chans[i].group[0]) {
            if (chans[i].file == 0) wcscpy(chans[i].group, L"Mes cha\u00eenes");
            else { wcsncpy(chans[i].group, fileNames[chans[i].file], 95); wchar_t *d = wcsrchr(chans[i].group, L'.'); if (d) *d = 0; }
        }
        if (!in_list(i)) continue;
        int f = 0; for (int k = 0; k < nLangs; k++) if (!wcscmp(langs[k], chans[i].lang)) { f = 1; break; }
        if (!f && nLangs < 64) wcscpy(langs[nLangs++], chans[i].lang);
        if (!in_lang(i)) continue;
        f = 0; for (int k = 0; k < nCats; k++) if (!wcscmp(cats[k], chans[i].group)) { f = 1; break; }
        if (!f && nCats < 512) wcscpy(cats[nCats++], chans[i].group);
    }
    qsort(cats, nCats, sizeof cats[0], cat_cmp);
    qsort(langs, nLangs, sizeof langs[0], lang_cmp);
}
static void load_channels(void) { load_channels_raw(); if (migrate_playlists()) load_channels_raw(); build_cats(); }

#define GRP_MUSIC L"Musique"
static int wcs_has_ci(const wchar_t *h, const wchar_t *n) { size_t ln = wcslen(n); for (; *h; h++) { size_t k = 0; while (k < ln && h[k] && towlower(h[k]) == towlower(n[k])) k++; if (k == ln) return 1; } return 0; }
static int is_music(int i) { if (chans[i].file > 0 && chans[i].file < nFiles && !_wcsnicmp(fileNames[chans[i].file], L"musique", 7)) return 1;   /* playlist \u00ab Musique*.m3u \u00bb = webradios */
    if (chans[i].file != 0) return 0; if (!wcscmp(chans[i].group, GRP_MUSIC)) return 1; return (!chans[i].group[0] || !wcscmp(chans[i].group, L"Mes cha\u00eenes")) && wcs_has_ci(chans[i].name, L"radio"); }
static void save_own(int skip) {      /* reecrit mes_chaines.m3u (sans l'entree "skip") : ecriture atomique + copie de secours .bak */
    wchar_t full[MAX_PATH], tmp[MAX_PATH], bak[MAX_PATH];
    _snwprintf(full, MAX_PATH - 1, L"%s\\%s", iptvDir, MYFILE); full[MAX_PATH - 1] = 0;
    _snwprintf(tmp, MAX_PATH - 1, L"%s.tmp", full); tmp[MAX_PATH - 1] = 0;
    _snwprintf(bak, MAX_PATH - 1, L"%s.bak", full); bak[MAX_PATH - 1] = 0;
    HANDLE f = CreateFileW(tmp, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL); int ok = f != INVALID_HANDLE_VALUE;
    if (ok) {
        DWORD w; ok = WriteFile(f, "#EXTM3U\r\n", 9, &w, NULL);
        for (int i = 0; ok && i < nChans; i++) {
            if (chans[i].file != 0 || i == skip) continue;
            char n[400], line[1600]; w8(chans[i].name, n, sizeof n);
            char g[200] = ""; if (chans[i].group[0] && wcscmp(chans[i].group, L"Mes cha\u00eenes")) { char g8[160]; w8(chans[i].group, g8, sizeof g8); snprintf(g, sizeof g, " group-title=\"%s\"", g8); }
            int l = snprintf(line, sizeof line, "#EXTINF:-1%s,%s\r\n%s\r\n", g, n, chans[i].url);
            ok = WriteFile(f, line, l, &w, NULL) && w == (DWORD)l;
        }
        if (ok) ok = FlushFileBuffers(f);
        CloseHandle(f);
    }
    if (ok) {
        if (GetFileAttributesW(full) != INVALID_FILE_ATTRIBUTES) CopyFileW(full, bak, FALSE);
        ok = MoveFileExW(tmp, full, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH);
    }
    if (!ok) { DeleteFileW(tmp); MessageBoxW(owner_w(), L"Impossible d'enregistrer la liste des cha\u00eenes (dossier iptv prot\u00e9g\u00e9 en \u00e9criture ?).", L"IPTV", MB_ICONERROR); }
}

static int is_playlist_url(const char *u) {
    if (strncmp(u, "http://", 7) && strncmp(u, "https://", 8)) return 0;
    char t[1100]; strncpy(t, u, 1099); t[1099] = 0;
    char *q = strpbrk(t, "?#"); if (q) *q = 0;
    size_t l = strlen(t); return l > 4 && !_stricmp(t + l - 4, ".m3u");
}

static void safe_name(const wchar_t *name, wchar_t *out) {
    int k = 0;
    for (const wchar_t *p = name; *p && k < 100; p++) out[k++] = wcschr(L"\\/:*?\"<>|", *p) ? L'_' : *p;
    while (k && (out[k - 1] == L' ' || out[k - 1] == L'.')) k--;
    if (!k) { wcscpy(out, L"playlist"); k = 8; }
    out[k] = 0; wcscat(out, L".m3u");
}

static int download_playlist(const wchar_t *url, const wchar_t *dest) {
    wchar_t tmp[MAX_PATH]; _snwprintf(tmp, MAX_PATH - 1, L"%s.tmp", dest); tmp[MAX_PATH - 1] = 0;
    DeleteUrlCacheEntryW(url);
    if (FAILED(URLDownloadToFileW(NULL, url, tmp, 0, NULL))) { DeleteFileW(tmp); return 0; }
    char head[4096] = ""; DWORD rd = 0;
    HANDLE f = CreateFileW(tmp, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (f != INVALID_HANDLE_VALUE) { ReadFile(f, head, sizeof head - 1, &rd, NULL); head[rd] = 0; CloseHandle(f); }
    if (!strstr(head, "#EXTM3U") && !strstr(head, "#EXTINF")) { DeleteFileW(tmp); return 0; }
    return MoveFileExW(tmp, dest, MOVEFILE_REPLACE_EXISTING) != 0;
}

/* sources.txt : "fichier|url" pour pouvoir actualiser les playlists distantes */
static void sources_rewrite(const wchar_t *drop, const wchar_t *addFile, const wchar_t *addUrl) {
    wchar_t sp[MAX_PATH]; _snwprintf(sp, MAX_PATH - 1, L"%s\\sources.txt", iptvDir); sp[MAX_PATH - 1] = 0;
    char *old = read_all(sp); char dropU[300] = "", out[60000]; int o = 0; out[0] = 0;
    if (drop) { w8(drop, dropU, sizeof dropU); strcat(dropU, "|"); }
    if (addFile) { w8(addFile, dropU, sizeof dropU); strcat(dropU, "|"); }
    if (old) {
        char *p = old;
        while (*p) {
            char *e = strchr(p, '\n'); size_t len = e ? (size_t)(e - p) : strlen(p);
            char line[1300]; if (len > 1299) len = 1299; memcpy(line, p, len); line[len] = 0;
            while (len && (line[len - 1] == '\r')) line[--len] = 0;
            p = e ? e + 1 : p + strlen(p);
            if (!len || (dropU[0] && !strncmp(line, dropU, strlen(dropU)))) continue;
            if (o + (int)len + 3 < (int)sizeof out) o += snprintf(out + o, sizeof out - o, "%s\r\n", line);
        }
        free(old);
    }
    if (addFile && addUrl) { char f[300], u[1100]; w8(addFile, f, sizeof f); w8(addUrl, u, sizeof u); o += snprintf(out + o, sizeof out - o, "%s|%s\r\n", f, u); }
    HANDLE h = CreateFileW(sp, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
    if (h != INVALID_HANDLE_VALUE) { DWORD w; WriteFile(h, out, o, &w, NULL); CloseHandle(h); }
}

static int refresh_sources(void) {
    wchar_t sp[MAX_PATH]; _snwprintf(sp, MAX_PATH - 1, L"%s\\sources.txt", iptvDir); sp[MAX_PATH - 1] = 0;
    char *t = read_all(sp); if (!t) return 0;
    int ok = 0; char *p = t;
    while (*p) {
        char *e = strchr(p, '\n'); size_t len = e ? (size_t)(e - p) : strlen(p);
        char line[1300]; if (len > 1299) len = 1299; memcpy(line, p, len); line[len] = 0;
        while (len && line[len - 1] == '\r') line[--len] = 0;
        p = e ? e + 1 : p + strlen(p);
        char *bar = strchr(line, '|'); if (!bar) continue; *bar = 0;
        wchar_t fw[300], uw[1100], dest[MAX_PATH]; u8w(line, fw, 300); u8w(bar + 1, uw, 1100);
        _snwprintf(dest, MAX_PATH - 1, L"%s\\%s", iptvDir, fw); dest[MAX_PATH - 1] = 0;
        if (download_playlist(uw, dest)) ok++;
    }
    free(t); return ok;
}

/* ajoute une playlist distante : telechargement + lecture des categories */
static void add_playlist(const wchar_t *name, const wchar_t *url) {
    wchar_t fn[160], dest[MAX_PATH]; safe_name(name, fn);
    _snwprintf(dest, MAX_PATH - 1, L"%s\\%s", iptvDir, fn); dest[MAX_PATH - 1] = 0;
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT));
    int ok = download_playlist(url, dest);
    SetCursor(old);
    if (!ok) { MessageBoxW(owner_w(), L"Téléchargement impossible (adresse invalide, ou ce n'est pas une playlist M3U).", L"IPTV", MB_ICONERROR); return; }
    sources_rewrite(NULL, fn, url);
}

/* anciennes "chaines" qui sont en fait des playlists .m3u distantes -> converties en playlist */
static int migrate_playlists(void) {
    static int tried = 0; if (tried) return 0; tried = 1;
    int changed = 0;
    for (int i = 0; i < nChans; i++) {
        if (chans[i].file != 0 || !is_playlist_url(chans[i].url)) continue;
        wchar_t u[1100], fn[160], dest[MAX_PATH]; u8w(chans[i].url, u, 1100); safe_name(chans[i].name, fn);
        _snwprintf(dest, MAX_PATH - 1, L"%s\\%s", iptvDir, fn); dest[MAX_PATH - 1] = 0;
        HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT));
        int ok = download_playlist(u, dest); SetCursor(old);
        if (ok) { sources_rewrite(NULL, fn, u); chans[i].file = -1; changed = 1; }
    }
    if (changed) save_own(-1);
    return changed;
}

static void play_channel(int i) {
    wchar_t u[1100]; u8w(chans[i].url, u, 1100);
    load_file(u);
    wcsncpy(chanTitle, chans[i].name, 255); chanTitle[255] = 0;
}

/* ----- petite fenêtre de saisie (nom + URL) ----- */
#define ID_NAME 101
#define ID_URL  102
static HWND hDlg, hEdName, hEdUrl;
static int dlgState;
static wchar_t dlgName[256], dlgUrl[1100];
static int dlgMusic, dlgShowMusic;
static HBRUSH brDlg, brEdit;

static void draw_btn(const DRAWITEMSTRUCT *d, int accent) {
    wchar_t t[64]; GetWindowTextW(d->hwndItem, t, 64);
    int dis = (d->itemState & ODS_DISABLED) != 0; RECT r = d->rcItem;
    fill(d->hDC, &r, dis ? C_BAR : ((d->itemState & ODS_SELECTED) ? C_TROU : C_HOT));
    if (accent && !dis) frect(d->hDC, r.left, r.bottom - 2, r.right, r.bottom, C_ACC);
    text(d->hDC, t, &r, dis ? C_DIM : (accent ? C_ACC : C_FG), fUI, DT_CENTER);
}

static void draw_check(const DRAWITEMSTRUCT *d, int on) {
    RECT r = d->rcItem; fill(d->hDC, &r, C_BAR);
    int by = (r.top + r.bottom) / 2, bx = r.left + S(2);
    frect(d->hDC, bx, by - S(8), bx + S(16), by + S(8), on ? C_ACC : C_TROU);
    if (on) { HPEN pn = CreatePen(PS_SOLID, S(2), C_BG), op = SelectObject(d->hDC, pn); MoveToEx(d->hDC, bx + S(3), by, NULL); LineTo(d->hDC, bx + S(7), by + S(4)); LineTo(d->hDC, bx + S(13), by - S(4)); SelectObject(d->hDC, op); DeleteObject(pn); }
    RECT t = r; t.left = bx + S(26); text(d->hDC, L"Cha\u00eene musicale / radio  (fond anim\u00e9 en vagues)", &t, C_FG, fUI, DT_LEFT);
}
static LRESULT CALLBACK DlgProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CTLCOLOREDIT: SetTextColor((HDC)wp, C_FG); SetBkColor((HDC)wp, C_BG); return (LRESULT)brEdit;
    case WM_CTLCOLORSTATIC: SetTextColor((HDC)wp, C_DIM); SetBkMode((HDC)wp, TRANSPARENT); return (LRESULT)brDlg;
    case WM_DRAWITEM: if (((DRAWITEMSTRUCT *)lp)->CtlID == 90) draw_check((DRAWITEMSTRUCT *)lp, dlgMusic); else draw_btn((DRAWITEMSTRUCT *)lp, ((DRAWITEMSTRUCT *)lp)->CtlID == IDOK); return TRUE;
    case WM_COMMAND:
        if (LOWORD(wp) == 90) { dlgMusic = !dlgMusic; InvalidateRect((HWND)lp, NULL, TRUE); }
        else if (LOWORD(wp) == IDOK) { GetWindowTextW(hEdName, dlgName, 256); GetWindowTextW(hEdUrl, dlgUrl, 1100); dlgState = 1; }
        else if (LOWORD(wp) == IDCANCEL) dlgState = 2;
        return 0;
    case WM_CLOSE: dlgState = 2; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

static int ask_entry(const wchar_t *ttl, const wchar_t *l1, const wchar_t *l2, const wchar_t *hint, const wchar_t *okt) {
    static int reg = 0;
    if (!reg) {
        brDlg = CreateSolidBrush(C_BAR); brEdit = CreateSolidBrush(C_BG);
        WNDCLASSW wc; memset(&wc, 0, sizeof wc);
        wc.lpfnWndProc = DlgProc; wc.hInstance = hInst; wc.lpszClassName = L"LavDlg";
        wc.hbrBackground = brDlg; wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hIcon = LoadIconW(hInst, MAKEINTRESOURCEW(1));
        RegisterClassW(&wc); reg = 1;
    }
    HWND oh_ = dlgOwner ? dlgOwner : hMain;
    dlgState = 0; dlgName[0] = dlgUrl[0] = 0;
    hDlg = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LavDlg", L"Ajouter une chaîne IPTV", WS_POPUP | WS_CAPTION | WS_SYSMENU,
                           0, 0, 300, 200, oh_, NULL, hInst, NULL);
    int cw = S(520), ch = S(212);
    RECT wr, cr; GetWindowRect(hDlg, &wr); GetClientRect(hDlg, &cr);
    int ow = (wr.right - wr.left) - cr.right + cw, oh = (wr.bottom - wr.top) - cr.bottom + ch;
    RECT mr; GetWindowRect(oh_, &mr);
    SetWindowPos(hDlg, NULL, mr.left + ((mr.right - mr.left) - ow) / 2, mr.top + ((mr.bottom - mr.top) - oh) / 2, ow, oh, SWP_NOZORDER);
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute");
               if (f) { f(hDlg, 20, &dark, sizeof dark); f(hDlg, 19, &dark, sizeof dark); } }
    HWND c;
    c = CreateWindowExW(0, L"STATIC", L"Nom de la chaîne", WS_CHILD | WS_VISIBLE, S(16), S(12), S(480), S(18), hDlg, NULL, hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
    hEdName = CreateWindowExW(0, L"EDIT", L"", WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL, S(16), S(34), S(488), S(26), hDlg, (HMENU)ID_NAME, hInst, NULL); SendMessage(hEdName, WM_SETFONT, (WPARAM)fUI, 1);
    c = CreateWindowExW(0, L"STATIC", L"Adresse du flux  (http, https, rtmp, rtsp, udp, m3u8, playlist .m3u…)", WS_CHILD | WS_VISIBLE, S(16), S(72), S(488), S(18), hDlg, NULL, hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
    hEdUrl = CreateWindowExW(0, L"EDIT", L"", WS_CHILD | WS_VISIBLE | WS_TABSTOP | WS_BORDER | ES_AUTOHSCROLL, S(16), S(94), S(488), S(26), hDlg, (HMENU)ID_URL, hInst, NULL); SendMessage(hEdUrl, WM_SETFONT, (WPARAM)fUI, 1);
    if (dlgShowMusic) CreateWindowExW(0, L"BUTTON", L"", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(16), S(128), S(488), S(28), hDlg, (HMENU)90, hInst, NULL);
    else {
    c = CreateWindowExW(0, L"STATIC", L"Enregistrée dans le dossier iptv, puis lue immédiatement.", WS_CHILD | WS_VISIBLE, S(16), S(132), S(488), S(18), hDlg, NULL, hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fSmall, 1);
    }
    c = CreateWindowExW(0, L"BUTTON", okt, WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(298), S(166), S(100), S(30), hDlg, (HMENU)IDOK, hInst, NULL);
    c = CreateWindowExW(0, L"BUTTON", L"Annuler", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(404), S(166), S(100), S(30), hDlg, (HMENU)IDCANCEL, hInst, NULL);
    SendMessage(hDlg, DM_SETDEFID, IDOK, 0);
    if (dlgPreName[0]) SetWindowTextW(hEdName, dlgPreName);
    if (dlgPreUrl[0]) SetWindowTextW(hEdUrl, dlgPreUrl);
    if (dlgNameRO) SendMessage(hEdName, EM_SETREADONLY, TRUE, 0);
    int prevMenu = menuOpen; menuOpen = 1; EnableWindow(oh_, FALSE);
    ShowWindow(hDlg, SW_SHOW); SetForegroundWindow(hDlg); SetFocus(hEdName);
    MSG msg;
    while (dlgState == 0) {
        int r = GetMessage(&msg, NULL, 0, 0);
        if (r <= 0) { if (r == 0) PostQuitMessage((int)msg.wParam); dlgState = 2; break; }
        if (!IsDialogMessage(hDlg, &msg)) { TranslateMessage(&msg); DispatchMessage(&msg); }
    }
    EnableWindow(oh_, TRUE); DestroyWindow(hDlg); hDlg = NULL; menuOpen = prevMenu;
    SetForegroundWindow(oh_);
    dlgPreName[0] = dlgPreUrl[0] = 0; dlgNameRO = 0; dlgShowMusic = 0;
    return dlgState == 1;
}

static int ask_channel(void) {
    dlgShowMusic = 1; dlgMusic = 0;
    return ask_entry(L"Ajouter une cha\u00eene IPTV", L"Nom de la cha\u00eene",
                     L"Adresse du flux  (http, https, rtmp, rtsp, udp, m3u8\u2026)",
                     L"Enregistr\u00e9e dans le dossier iptv, puis lue imm\u00e9diatement.", L"Ajouter");
}
static int ask_playlist(void) {
    return ask_entry(L"Ajouter une playlist IPTV", L"Nom de la playlist",
                     L"Adresse de la playlist  (.m3u ou .m3u8, ex. https://iptv-org.github.io/iptv/index.m3u)",
                     L"T\u00e9l\u00e9charg\u00e9e dans le dossier iptv : cat\u00e9gories et cha\u00eenes lues automatiquement.", L"Ajouter");
}

static void esc_amp(const wchar_t *src, wchar_t *dst, int cap) {
    int k = 0;
    for (const wchar_t *p = src; *p && k < cap - 3 && (p - src) < 90; p++) { dst[k++] = *p; if (*p == L'&') dst[k++] = L'&'; }
    dst[k] = 0;
}

static int run_menu(HMENU m, RECT anchor) {
    HWND ph = cur_panel(); POINT p = { anchor.left, anchor.top }; ClientToScreen(ph, &p);
    menuOpen = 1;
    int c = TrackPopupMenu(m, TPM_BOTTOMALIGN | TPM_LEFTALIGN | TPM_RETURNCMD, p.x, p.y - S(2), 0, ph, NULL);
    menuOpen = 0; DestroyMenu(m); SetFocus(hMain);
    return c;
}
static void add_item(HMENU m, int i, const char *cur) {
    wchar_t t[256]; esc_amp(chans[i].name, t, 256);
    AppendMenuW(m, MF_STRING | (cur && !strcmp(cur, chans[i].url) ? MF_CHECKED : 0), 5000 + i, t);
}

static void iptv_exec(int c) {
    if (c >= 5000 && c < 5000 + nChans) play_channel(c - 5000);
    else if (c == 4000) {
        if (ask_channel()) {
            wchar_t *u = dlgUrl; while (*u == L' ') u++;
            char u8[1100]; w8(u, u8, sizeof u8);
            if (*u && is_playlist_url(u8)) {           /* .m3u distant : c'est une playlist, pas un flux */
                if (!dlgName[0]) wcsncpy(dlgName, L"playlist", 120);
                add_playlist(dlgName, u); load_channels(); selCat[0] = 0; inval(); return;
            }
            if (*u) {
                if (!dlgName[0]) wcsncpy(dlgName, u, 120);
                load_channels();
                if (!ensure_cap()) return;
                Chan *n = &chans[nChans]; memset(n, 0, sizeof *n);
                wcsncpy(n->name, dlgName, 127); w8(u, n->url, 1024); n->file = 0; if (dlgMusic) wcscpy(n->group, GRP_MUSIC);
                nChans++; save_own(-1); load_channels();
                for (int i = nChans - 1; i >= 0; i--) if (chans[i].file == 0) { play_channel(i); break; }
            }
        }
    }
    else if (c == 4003) {
        if (ask_playlist()) {
            wchar_t *u = dlgUrl; while (*u == L' ') u++;
            if (*u) {
                if (!dlgName[0]) wcsncpy(dlgName, L"playlist", 120);
                add_playlist(dlgName, u); load_channels(); selCat[0] = 0;
                wchar_t fn[160]; safe_name(dlgName, fn); int n = 0, k = 0; wchar_t seen[64][96];
                for (int i = 0; i < nChans; i++) if (chans[i].file > 0 && !_wcsicmp(fileNames[chans[i].file], fn)) {
                    n++; int f = 0; for (int j = 0; j < k; j++) if (!wcscmp(seen[j], chans[i].group)) { f = 1; break; }
                    if (!f && k < 64) wcscpy(seen[k++], chans[i].group);
                }
                wchar_t msg[260]; _snwprintf(msg, 259, L"Playlist ajout\u00e9e : %d cha\u00eene(s).\nUtilisez les s\u00e9lecteurs Cat\u00e9gorie puis Cha\u00eene.", n); msg[259] = 0;
                if (n) MessageBoxW(owner_w(), msg, L"IPTV", MB_ICONINFORMATION);
            }
        }
    }
    else if (c == 4004) {
        HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ok = refresh_sources(); SetCursor(old);
        load_channels();
        wchar_t msg[100]; _snwprintf(msg, 99, L"%d playlist(s) actualis\u00e9e(s).", ok); msg[99] = 0; MessageBoxW(owner_w(), msg, L"IPTV", MB_ICONINFORMATION);
    }
    else if (c >= 20000 && c < 20064) {
        int f = c - 20000; wchar_t q[300]; _snwprintf(q, 299, L"Supprimer la playlist \u00ab %s \u00bb ?", fileNames[f]); q[299] = 0;
        if (f < nFiles && MessageBoxW(owner_w(), q, L"IPTV", MB_YESNO | MB_ICONQUESTION) == IDYES) {
            wchar_t p[MAX_PATH]; _snwprintf(p, MAX_PATH - 1, L"%s\%s", iptvDir, fileNames[f]); p[MAX_PATH - 1] = 0;
            DeleteFileW(p); sources_rewrite(fileNames[f], NULL, NULL); selCat[0] = 0; selLang[0] = 0; selList[0] = 0; save_sel(); load_channels();
        }
    }
    else if (c == 4001) {
        wchar_t buf[MAX_PATH] = L""; OPENFILENAMEW o; memset(&o, 0, sizeof o);
        o.lStructSize = sizeof o; o.hwndOwner = hMain; o.lpstrFile = buf; o.nMaxFile = MAX_PATH;
        o.lpstrFilter = L"Playlists\0*.m3u;*.m3u8;*.txt\0Tous les fichiers\0*.*\0";
        o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
        if (GetOpenFileNameW(&o)) {
            wchar_t *b = wcsrchr(buf, L'\\'); b = b ? b + 1 : buf;
            wchar_t dst[MAX_PATH]; _snwprintf(dst, MAX_PATH - 1, L"%s\\%s", iptvDir, b); dst[MAX_PATH - 1] = 0;
            if (CopyFileW(buf, dst, FALSE)) {
                load_channels(); int n = 0;
                for (int i = 0; i < nChans; i++) if (chans[i].file > 0 && !_wcsicmp(fileNames[chans[i].file], b)) n++;
                wchar_t msg[200]; _snwprintf(msg, 199, L"Playlist importée : %d chaîne(s).\nUtilisez les sélecteurs Catégorie / Chaîne.", n); msg[199] = 0;
                MessageBoxW(owner_w(), msg, L"IPTV", MB_ICONINFORMATION);
            } else MessageBoxW(owner_w(), L"Import impossible.", L"IPTV", MB_ICONERROR);
        }
    }
    else if (c == 4002) ShellExecuteW(NULL, L"open", iptvDir, NULL, NULL, SW_SHOWNORMAL);
    else if (c >= 9000 && c < 9000 + nChans) {
        wchar_t q[300]; _snwprintf(q, 299, L"Supprimer « %s » ?", chans[c - 9000].name); q[299] = 0;
        if (MessageBoxW(owner_w(), q, L"IPTV", MB_YESNO | MB_ICONQUESTION) == IDYES) { save_own(c - 9000); load_channels(); }
    }
    inval();
}

/* bouton IPTV : listes IPTV, puis chaines musicales (par leur nom) */
static void iptv_menu(void) {
    iptv_init_dir(); load_channels();
    HMENU m = CreatePopupMenu(); int total = 0, nMus = 0, cnt[64]; memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < nChans; i++) { if (is_music(i)) { nMus++; continue; } if (chans[i].file >= 0 && chans[i].file < 64) cnt[chans[i].file]++; }
    for (int f = 0; f < nFiles && f < 64; f++) if (cnt[f]) total++;
    if (total) {
        AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"IPTV");
        AppendMenuW(m, MF_STRING | (selList[0] ? 0 : MF_CHECKED), 8000, L"Toutes les listes");
        for (int f = 0; f < nFiles && f < 64; f++) {
            int n = cnt[f]; if (!n) continue;
            wchar_t base[MAX_PATH], e[MAX_PATH], t[MAX_PATH + 24];
            if (f == 0) wcscpy(base, L"Mes cha\u00eenes"); else { wcscpy(base, fileNames[f]); wchar_t *d = wcsrchr(base, L'.'); if (d) *d = 0; }
            esc_amp(base, e, MAX_PATH); _snwprintf(t, MAX_PATH + 23, L"%s  (%d)", e, n); t[MAX_PATH + 23] = 0;
            AppendMenuW(m, MF_STRING | (!_wcsicmp(selList, fileNames[f]) ? MF_CHECKED : 0), 8100 + f, t);
        }
    }
    if (nMus) {
        if (total) AppendMenuW(m, MF_SEPARATOR, 0, NULL);
        AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"MUSIQUE");
        for (int i = 0; i < nChans && i < 2900; i++) if (is_music(i)) {
            wchar_t e[256]; esc_amp(chans[i].name, e, 256);
            AppendMenuW(m, MF_STRING | (playing && !wcscmp(chanTitle, chans[i].name) ? MF_CHECKED : 0), 5000 + i, e);
        }
    }
    if (!total && !nMus) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune liste IPTV");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    AppendMenuW(m, MF_STRING, 8999, L"Gérer les listes…");
    int c = run_menu(m, rIptv);
    if (c == 8999) { manage_window(); return; }
    if (c >= 5000 && c < 5000 + nChans && c < 7900) { play_channel(c - 5000); inval(); return; }
    if (c == 8000 || (c >= 8100 && c < 8100 + nFiles)) {
        if (c == 8000) selList[0] = 0; else wcscpy(selList, fileNames[c - 8100]);
        selLang[0] = 0; selCat[0] = 0; build_cats(); save_sel(); inval();
        if (nLangs > 1) lang_menu(); else cat_menu();      /* enchaine sur le choix suivant */
    }
}

/* persistance de la selection (langue / categorie) */
static void sel_path(wchar_t *p) { _snwprintf(p, MAX_PATH - 1, L"%s\\selection.txt", iptvDir); p[MAX_PATH - 1] = 0; }
static void save_sel(void) {
    wchar_t sp[MAX_PATH]; sel_path(sp); char l[200], c[300], li[300], out[900];
    w8(selLang, l, sizeof l); w8(selCat, c, sizeof c); w8(selList, li, sizeof li);
    int n = snprintf(out, sizeof out, "%s\r\n%s\r\n%s\r\n", l, c, li);
    HANDLE h = CreateFileW(sp, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
    if (h != INVALID_HANDLE_VALUE) { DWORD w; WriteFile(h, out, n, &w, NULL); CloseHandle(h); }
}
static void load_sel(void) {
    wchar_t sp[MAX_PATH]; sel_path(sp); char *t = read_all(sp); if (!t) return;
    char *ln[3] = { t, NULL, NULL }; char *p = t;
    for (int k = 0; k < 3; k++) {
        ln[k] = p; char *e = strchr(p, '\n'); if (e) { *e = 0; p = e + 1; } else p += strlen(p);
        size_t l = strlen(ln[k]); while (l && ln[k][l - 1] == '\r') ln[k][--l] = 0;
    }
    u8w(ln[0], selLang, 48); u8w(ln[1], selCat, 96); u8w(ln[2], selList, MAX_PATH); free(t);
}

/* selecteur de langue */
static void lang_menu(void) {
    iptv_init_dir(); load_channels();
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | (selLang[0] ? 0 : MF_CHECKED), 7000, L"Toutes les langues");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    for (int k = 0; k < nLangs; k++) {
        int n = 0; for (int i = 0; i < nChans; i++) if (in_list(i) && !wcscmp(chans[i].lang, langs[k])) n++;
        wchar_t e[100], t[140]; esc_amp(langs[k], e, 100); _snwprintf(t, 139, L"%s  (%d)", e, n); t[139] = 0;
        AppendMenuW(m, MF_STRING | (!wcscmp(selLang, langs[k]) ? MF_CHECKED : 0), 7001 + k, t);
    }
    if (!nLangs) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune langue (ajoutez ou importez des chaînes)");
    int c = run_menu(m, rLang);
    if (c == 7000 || (c >= 7001 && c < 7001 + nLangs)) {
        if (c == 7000) selLang[0] = 0; else wcscpy(selLang, langs[c - 7001]);
        selCat[0] = 0; build_cats(); save_sel(); inval();
        cat_menu();                                   /* enchaine sur les categories de cette langue */
    }
}

/* selecteur de categorie */
static void cat_menu(void) {
    iptv_init_dir(); load_channels();
    HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | (selCat[0] ? 0 : MF_CHECKED), 6000, L"Toutes les catégories");
    AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    for (int k = 0; k < nCats; k++) {
        int n = 0; for (int i = 0; i < nChans; i++) if (in_lang(i) && !wcscmp(chans[i].group, cats[k])) n++;
        wchar_t e[200], t[240]; esc_amp(cats[k], e, 200); _snwprintf(t, 239, L"%s  (%d)", e, n); t[239] = 0;
        AppendMenuW(m, MF_STRING | (!wcscmp(selCat, cats[k]) ? MF_CHECKED : 0), 6001 + k, t);
    }
    if (!nCats) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune catégorie (ajoutez ou importez des chaînes)");
    int c = run_menu(m, rCat);
    if (c == 6000) selCat[0] = 0;
    else if (c >= 6001 && c < 6001 + nCats) wcscpy(selCat, cats[c - 6001]);
    save_sel(); inval();
    if (c >= 6000 && c < 6001 + nCats) chan_menu();   /* enchaine sur la liste des cha\u00eenes de cette cat\u00e9gorie */
}

/* selecteur de chaine (de la categorie choisie ; par lettre si la liste est longue) */
static void chan_menu(void) {
    iptv_init_dir(); load_channels();
    HMENU m = CreatePopupMenu(); char *cur = p_get_property_string(mpv, "path"); int n = 0;
    for (int i = 0; i < nChans; i++) if (in_lang(i) && (!selCat[0] || !wcscmp(chans[i].group, selCat))) n++;
    if (!n) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune chaîne dans cette catégorie");
    else if (n <= 80) { for (int i = 0; i < nChans; i++) if (in_lang(i) && (!selCat[0] || !wcscmp(chans[i].group, selCat))) add_item(m, i, cur); }
    else {
        for (int b = 0; b <= 26; b++) {
            HMENU sm = CreatePopupMenu(); int cnt = 0;
            for (int i = 0; i < nChans; i++) {
                if (!in_lang(i) || (selCat[0] && wcscmp(chans[i].group, selCat))) continue;
                wchar_t ch = towupper(chans[i].name[0]); int idx = (ch >= L'A' && ch <= L'Z') ? ch - L'A' : 26;
                if (idx == b) { add_item(sm, i, cur); cnt++; }
            }
            if (cnt) { wchar_t t[32]; if (b < 26) _snwprintf(t, 31, L"%c  (%d)", L'A' + b, cnt); else _snwprintf(t, 31, L"#  (%d)", cnt);
                       t[31] = 0; AppendMenuW(m, MF_POPUP, (UINT_PTR)sm, t); }
            else DestroyMenu(sm);
        }
    }
    if (cur) p_free(cur);
    iptv_exec(run_menu(m, rChan));
}


/* ================= fenetre de gestion IPTV ================= */
enum { M_ADDC = 301, M_ADDP, M_IMP, M_EDIT, M_REPL, M_REF, M_DEL, M_EXP, M_IMPZ, M_DIR };
static HWND hLv, mgrBtn[12];
static volatile int rowState[1024];       /* 0 = test en cours, 1 = en ligne, 2 = hors ligne, 3 = non testable */
static volatile LONG mgrGen;
#define WM_MGR_STATE (WM_APP + 20)
typedef struct { int n, gen; int kind[256]; char url[256][1100]; } CheckSet;
static int check_url(const char *url) {
    HINTERNET ses = InternetOpenA("VLC/3.0.20 LibVLC/3.0.20", INTERNET_OPEN_TYPE_PRECONFIG, NULL, NULL, 0); if (!ses) return 2;
    DWORD to = 6000; InternetSetOptionA(ses, INTERNET_OPTION_CONNECT_TIMEOUT, &to, sizeof to); InternetSetOptionA(ses, INTERNET_OPTION_RECEIVE_TIMEOUT, &to, sizeof to);
    HINTERNET u = InternetOpenUrlA(ses, url, NULL, 0, INTERNET_FLAG_RELOAD | INTERNET_FLAG_NO_CACHE_WRITE | INTERNET_FLAG_NO_UI, 0);
    int st = 2;
    if (u) { DWORD code = 0, len = sizeof code; if (HttpQueryInfoA(u, HTTP_QUERY_STATUS_CODE | HTTP_QUERY_FLAG_NUMBER, &code, &len, NULL) && code >= 200 && code < 400) st = 1; InternetCloseHandle(u); }
    InternetCloseHandle(ses); return st;
}
static DWORD WINAPI check_thread(LPVOID a) {
    CheckSet *c = (CheckSet *)a; HWND h = hMgr;
    for (int k = 0; k < c->n; k++) {
        if (c->kind[k] != 1) continue;
        int st = check_url(c->url[k]);
        if (c->gen != mgrGen || !IsWindow(h)) break;
        PostMessage(h, WM_MGR_STATE, k, st);
    }
    free(c); return 0;
}
static int mgrDone;
static wchar_t mgrFiles[64][MAX_PATH];

static int get_source(const wchar_t *file, wchar_t *out, int cap) {
    out[0] = 0; wchar_t sp[MAX_PATH]; _snwprintf(sp, MAX_PATH - 1, L"%s\\sources.txt", iptvDir); sp[MAX_PATH - 1] = 0;
    char *t = read_all(sp); if (!t) return 0;
    char f8[320]; w8(file, f8, 300); strcat(f8, "|"); size_t fl = strlen(f8); char *p = t; int found = 0;
    while (*p) {
        char *e = strchr(p, '\n'); size_t len = e ? (size_t)(e - p) : strlen(p);
        char line[1300]; if (len > 1299) len = 1299; memcpy(line, p, len); line[len] = 0;
        while (len && line[len - 1] == '\r') line[--len] = 0;
        p = e ? e + 1 : p + strlen(p);
        if (!strncmp(line, f8, fl)) { u8w(line + fl, out, cap); found = 1; break; }
    }
    free(t); return found;
}

static void mgr_fill(void) {
    load_channels(); ListView_DeleteAllItems(hLv);
    int row = 0; LONG gen = InterlockedIncrement(&mgrGen);
    CheckSet *cs = (CheckSet *)calloc(1, sizeof(CheckSet)); cs->gen = (int)gen;
    for (int i = 0; i < 1024; i++) rowState[i] = 0;
    for (int i = 0; i < nChans; i++) if (chans[i].file == 0 && row < 256) {
        LVITEM it; memset(&it, 0, sizeof it); it.mask = LVIF_TEXT | LVIF_PARAM; it.iItem = row; it.pszText = chans[i].name; it.lParam = i;
        int r = ListView_InsertItem(hLv, &it);
        wchar_t u[1100]; u8w(chans[i].url, u, 1100);
        ListView_SetItemText(hLv, r, 1, L"Chaîne"); ListView_SetItemText(hLv, r, 2, L"1"); ListView_SetItemText(hLv, r, 3, u);
        if (!strncmp(chans[i].url, "http://", 7) || !strncmp(chans[i].url, "https://", 8)) { cs->kind[row] = 1; strncpy(cs->url[row], chans[i].url, 1099); } else rowState[row] = 3;
        row++;
    }
    for (int f = 1; f < nFiles && row < 256; f++) {
        wcscpy(mgrFiles[f], fileNames[f]);
        wchar_t base[MAX_PATH]; wcscpy(base, fileNames[f]); wchar_t *d = wcsrchr(base, L'.'); if (d) *d = 0;
        int n = 0; for (int i = 0; i < nChans; i++) if (chans[i].file == f) n++;
        wchar_t cnt[16], src[1100]; _snwprintf(cnt, 15, L"%d", n); cnt[15] = 0;
        int remote = get_source(fileNames[f], src, 1100); if (!remote) wcscpy(src, L"Fichier local");
        LVITEM it; memset(&it, 0, sizeof it); it.mask = LVIF_TEXT | LVIF_PARAM; it.iItem = row; it.pszText = base; it.lParam = 100000 + f;
        int r = ListView_InsertItem(hLv, &it);
        ListView_SetItemText(hLv, r, 1, L"Playlist"); ListView_SetItemText(hLv, r, 2, cnt); ListView_SetItemText(hLv, r, 3, src);
        if (remote) { cs->kind[row] = 1; w8(src, cs->url[row], 1100); } else rowState[row] = n ? 1 : 2;
        row++;
    }
    cs->n = row;
    if (row) CloseHandle(CreateThread(NULL, 0, check_thread, cs, 0, NULL)); else free(cs);
}

static int mgr_get(int *pl, int *idx) {
    int s = ListView_GetNextItem(hLv, -1, LVNI_SELECTED); if (s < 0) return 0;
    LVITEM it; memset(&it, 0, sizeof it); it.mask = LVIF_PARAM; it.iItem = s; ListView_GetItem(hLv, &it);
    if (it.lParam >= 100000) { *pl = 1; *idx = (int)it.lParam - 100000; } else { *pl = 0; *idx = (int)it.lParam; }
    return 1;
}

static void mgr_buttons(void) {
    int pl = 0, idx = 0, sel = mgr_get(&pl, &idx);
    EnableWindow(mgrBtn[M_EDIT - 301], sel); EnableWindow(mgrBtn[M_DEL - 301], sel); EnableWindow(mgrBtn[M_REPL - 301], sel && pl);
    for (int i = 0; i < 10; i++) InvalidateRect(mgrBtn[i], NULL, FALSE);
}

static wchar_t *trim(wchar_t *u) { while (*u == L' ') u++; size_t l = wcslen(u); while (l && u[l - 1] == L' ') u[--l] = 0; return u; }
static void dest_path(const wchar_t *file, wchar_t *d) { _snwprintf(d, MAX_PATH - 1, L"%s\\%s", iptvDir, file); d[MAX_PATH - 1] = 0; }

static void act_add_channel(void) {
    dlgOwner = hMgr;
    if (ask_channel()) {
        wchar_t *u = trim(dlgUrl); char u8[1100]; w8(u, u8, sizeof u8);
        if (*u && is_playlist_url(u8)) { if (!dlgName[0]) wcsncpy(dlgName, L"playlist", 120); add_playlist(dlgName, u); }
        else if (*u) {
            load_channels();
            if (ensure_cap()) {
                if (!dlgName[0]) wcsncpy(dlgName, u, 120);
                Chan *n = &chans[nChans]; memset(n, 0, sizeof *n); wcsncpy(n->name, dlgName, 127); w8(u, n->url, 1024); n->file = 0; if (dlgMusic) wcscpy(n->group, GRP_MUSIC);
                nChans++; save_own(-1);
            }
        }
    }
    dlgOwner = NULL;
}
static void act_add_playlist(void) {
    dlgOwner = hMgr;
    if (ask_playlist()) { wchar_t *u = trim(dlgUrl); if (*u) { if (!dlgName[0]) wcsncpy(dlgName, L"playlist", 120); add_playlist(dlgName, u); } }
    dlgOwner = NULL;
}
static void act_import(void) {
    wchar_t buf[MAX_PATH] = L""; OPENFILENAMEW o; memset(&o, 0, sizeof o);
    o.lStructSize = sizeof o; o.hwndOwner = hMgr; o.lpstrFile = buf; o.nMaxFile = MAX_PATH;
    o.lpstrFilter = L"Playlists\0*.m3u;*.m3u8;*.txt\0Tous les fichiers\0*.*\0"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetOpenFileNameW(&o)) return;
    wchar_t *b = wcsrchr(buf, L'\\'); b = b ? b + 1 : buf; wchar_t dst[MAX_PATH]; dest_path(b, dst);
    if (!CopyFileW(buf, dst, FALSE)) MessageBoxW(hMgr, L"Import impossible.", L"IPTV", MB_ICONERROR);
}
static void act_edit(void) {
    int pl, idx; if (!mgr_get(&pl, &idx)) return;
    dlgOwner = hMgr;
    if (!pl) {
        wcscpy(dlgPreName, chans[idx].name); u8w(chans[idx].url, dlgPreUrl, 1100);
        int wasMus = is_music(idx); dlgShowMusic = 1; dlgMusic = wasMus;
        if (ask_entry(L"Modifier la chaîne", L"Nom de la chaîne", L"Adresse du flux", L"Enregistré dans iptv\\mes_chaines.m3u.", L"Enregistrer")) {
            wchar_t *u = trim(dlgUrl);
            if (*u) { wcsncpy(chans[idx].name, dlgName[0] ? dlgName : u, 127); chans[idx].name[127] = 0; w8(u, chans[idx].url, 1024);
                  if (dlgMusic) wcscpy(chans[idx].group, GRP_MUSIC); else if (wasMus) wcscpy(chans[idx].group, L"TV"); save_own(-1); }
        }
    } else {
        wchar_t file[MAX_PATH], base[MAX_PATH], src[1100]; wcscpy(file, mgrFiles[idx]); wcscpy(base, file);
        wchar_t *d = wcsrchr(base, L'.'); if (d) *d = 0; get_source(file, src, 1100);
        wcscpy(dlgPreName, base); wcscpy(dlgPreUrl, src);
        if (ask_entry(L"Modifier la playlist", L"Nom de la playlist", L"Adresse de la playlist  (vide = playlist locale)",
                      L"Renommer la playlist et/ou changer son adresse source.", L"Enregistrer")) {
            wchar_t nf[160]; safe_name(dlgName[0] ? dlgName : base, nf);
            if (_wcsicmp(nf, file)) {
                wchar_t a[MAX_PATH], b[MAX_PATH]; dest_path(file, a); dest_path(nf, b);
                if (MoveFileExW(a, b, 0)) { sources_rewrite(file, NULL, NULL); wcscpy(file, nf); }
                else MessageBoxW(hMgr, L"Renommage impossible (ce nom existe déjà ?).", L"IPTV", MB_ICONERROR);
            }
            wchar_t *u = trim(dlgUrl);
            if (*u) {
                if (wcscmp(u, src)) {
                    wchar_t dst[MAX_PATH]; dest_path(file, dst); HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT));
                    int ok = download_playlist(u, dst); SetCursor(old);
                    if (ok) sources_rewrite(NULL, file, u); else MessageBoxW(hMgr, L"Téléchargement impossible : l'ancienne adresse est conservée.", L"IPTV", MB_ICONERROR);
                } else sources_rewrite(NULL, file, u);
            } else sources_rewrite(file, NULL, NULL);
        }
    }
    dlgOwner = NULL;
}
static void act_replace(void) {
    int pl, idx; if (!mgr_get(&pl, &idx) || !pl) return;
    wchar_t file[MAX_PATH], base[MAX_PATH], dst[MAX_PATH]; wcscpy(file, mgrFiles[idx]); wcscpy(base, file);
    wchar_t *d = wcsrchr(base, L'.'); if (d) *d = 0; dest_path(file, dst);
    wchar_t q[400]; _snwprintf(q, 399, L"Remplacer le contenu de « %s » :\n\nOui = depuis une adresse (URL)\nNon = depuis un fichier", base); q[399] = 0;
    int r = MessageBoxW(hMgr, q, L"Remplacer la playlist", MB_YESNOCANCEL | MB_ICONQUESTION);
    if (r == IDYES) {
        dlgOwner = hMgr; wcscpy(dlgPreName, base); dlgNameRO = 1;
        if (ask_entry(L"Remplacer la playlist", L"Playlist à remplacer", L"Nouvelle adresse de la playlist  (.m3u ou .m3u8)",
                      L"Son contenu est remplacé par celui de cette adresse.", L"Remplacer")) {
            wchar_t *u = trim(dlgUrl);
            if (*u) {
                HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ok = download_playlist(u, dst); SetCursor(old);
                if (ok) sources_rewrite(NULL, file, u); else MessageBoxW(hMgr, L"Téléchargement impossible : la playlist n'a pas été modifiée.", L"IPTV", MB_ICONERROR);
            }
        }
        dlgOwner = NULL;
    } else if (r == IDNO) {
        wchar_t buf[MAX_PATH] = L""; OPENFILENAMEW o; memset(&o, 0, sizeof o);
        o.lStructSize = sizeof o; o.hwndOwner = hMgr; o.lpstrFile = buf; o.nMaxFile = MAX_PATH;
        o.lpstrFilter = L"Playlists\0*.m3u;*.m3u8;*.txt\0Tous les fichiers\0*.*\0"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
        if (GetOpenFileNameW(&o)) { if (CopyFileW(buf, dst, FALSE)) sources_rewrite(file, NULL, NULL); else MessageBoxW(hMgr, L"Remplacement impossible.", L"IPTV", MB_ICONERROR); }
    }
}
static void act_refresh(void) {
    int pl = 0, idx = 0, sel = mgr_get(&pl, &idx); wchar_t msg[200];
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT));
    if (sel && pl) {
        wchar_t src[1100], dst[MAX_PATH]; get_source(mgrFiles[idx], src, 1100); dest_path(mgrFiles[idx], dst);
        if (!src[0]) { SetCursor(old); MessageBoxW(hMgr, L"Playlist locale : pas d'adresse source à actualiser.\nUtilisez « Remplacer… ».", L"IPTV", MB_ICONINFORMATION); return; }
        int ok = download_playlist(src, dst); SetCursor(old);
        MessageBoxW(hMgr, ok ? L"Playlist actualisée." : L"Actualisation impossible.", L"IPTV", ok ? MB_ICONINFORMATION : MB_ICONERROR);
    } else {
        int ok = refresh_sources(); SetCursor(old);
        _snwprintf(msg, 199, L"%d playlist(s) actualisée(s).", ok); msg[199] = 0; MessageBoxW(hMgr, msg, L"IPTV", MB_ICONINFORMATION);
    }
}
static void act_delete(void) {
    int pl, idx; if (!mgr_get(&pl, &idx)) return; wchar_t q[400];
    if (!pl) {
        _snwprintf(q, 399, L"Supprimer la chaîne « %s » ?", chans[idx].name); q[399] = 0;
        if (MessageBoxW(hMgr, q, L"IPTV", MB_YESNO | MB_ICONQUESTION) == IDYES) save_own(idx);
    } else {
        _snwprintf(q, 399, L"Supprimer la playlist « %s » ?", mgrFiles[idx]); q[399] = 0;
        if (MessageBoxW(hMgr, q, L"IPTV", MB_YESNO | MB_ICONQUESTION) == IDYES) {
            wchar_t p[MAX_PATH]; dest_path(mgrFiles[idx], p); DeleteFileW(p); sources_rewrite(mgrFiles[idx], NULL, NULL);
        }
    }
}


/* ----- export / import de la liste (zip, via tar.exe fourni avec Windows) ----- */
static int run_tar(const wchar_t *args) {
    wchar_t sys[MAX_PATH], cmdl[9000]; GetSystemDirectoryW(sys, MAX_PATH);
    _snwprintf(cmdl, 8999, L"\"%s\\tar.exe\" %s", sys, args); cmdl[8999] = 0;
    STARTUPINFOW si; memset(&si, 0, sizeof si); si.cb = sizeof si; PROCESS_INFORMATION pi;
    if (!CreateProcessW(NULL, cmdl, NULL, NULL, FALSE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi)) return -1;
    WaitForSingleObject(pi.hProcess, 90000); DWORD ec = 1; GetExitCodeProcess(pi.hProcess, &ec);
    CloseHandle(pi.hThread); CloseHandle(pi.hProcess); return (int)ec;
}
static void rm_tree(const wchar_t *dir) {
    wchar_t pat[MAX_PATH]; _snwprintf(pat, MAX_PATH - 1, L"%s\\*", dir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd);
    if (h != INVALID_HANDLE_VALUE) {
        do { if (!wcscmp(fd.cFileName, L".") || !wcscmp(fd.cFileName, L"..")) continue;
             wchar_t f[MAX_PATH]; _snwprintf(f, MAX_PATH - 1, L"%s\\%s", dir, fd.cFileName); f[MAX_PATH - 1] = 0;
             if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) rm_tree(f); else DeleteFileW(f);
        } while (FindNextFileW(h, &fd));
        FindClose(h);
    }
    RemoveDirectoryW(dir);
}
static int is_m3u_name(const wchar_t *n) { const wchar_t *e = wcsrchr(n, L'.'); return e && (!_wcsicmp(e, L".m3u") || !_wcsicmp(e, L".m3u8")); }
static int safe_file_name(const wchar_t *n) { return n[0] && !wcspbrk(n, L"\\/:*?\"<>|") && is_m3u_name(n); }

static void act_export(void) {
    wchar_t out[MAX_PATH] = L"iptv_export.zip"; OPENFILENAMEW o; memset(&o, 0, sizeof o);
    o.lStructSize = sizeof o; o.hwndOwner = hMgr; o.lpstrFile = out; o.nMaxFile = MAX_PATH; o.lpstrDefExt = L"zip";
    o.lpstrFilter = L"Archive ZIP\0*.zip\0"; o.Flags = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetSaveFileNameW(&o)) return;
    wchar_t args[8000], pat[MAX_PATH]; int n = 0;
    _snwprintf(args, 7999, L"-a -c -f \"%s\" -C \"%s\"", out, iptvDir); args[7999] = 0;
    _snwprintf(pat, MAX_PATH - 1, L"%s\\*", iptvDir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd);
    if (h != INVALID_HANDLE_VALUE) {
        do {
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) continue;
            if (is_m3u_name(fd.cFileName) || !_wcsicmp(fd.cFileName, L"sources.txt")) {
                size_t l = wcslen(args); if (l + wcslen(fd.cFileName) + 4 < 7900) { wcscat(args, L" \""); wcscat(args, fd.cFileName); wcscat(args, L"\""); n++; }
            }
        } while (FindNextFileW(h, &fd));
        FindClose(h);
    }
    if (!n) { MessageBoxW(hMgr, L"Rien à exporter : le dossier iptv est vide.", L"IPTV", MB_ICONINFORMATION); return; }
    DeleteFileW(out);
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ec = run_tar(args); SetCursor(old);
    if (ec == 0) { wchar_t m[200]; _snwprintf(m, 199, L"Liste exportée : %d fichier(s).", n); m[199] = 0; MessageBoxW(hMgr, m, L"IPTV", MB_ICONINFORMATION); }
    else MessageBoxW(hMgr, L"Export impossible (tar.exe de Windows requis : Windows 10 ou plus récent).", L"IPTV", MB_ICONERROR);
}

static int impCount;
static void import_walk(const wchar_t *dir) {
    wchar_t pat[MAX_PATH]; _snwprintf(pat, MAX_PATH - 1, L"%s\\*", dir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd); if (h == INVALID_HANDLE_VALUE) return;
    do {
        if (!wcscmp(fd.cFileName, L".") || !wcscmp(fd.cFileName, L"..")) continue;
        wchar_t full[MAX_PATH]; _snwprintf(full, MAX_PATH - 1, L"%s\\%s", dir, fd.cFileName); full[MAX_PATH - 1] = 0;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) { import_walk(full); continue; }
        if (!_wcsicmp(fd.cFileName, L"sources.txt")) {                         /* fusion des adresses sources */
            char *t = read_all(full); if (!t) continue; char *p = t;
            while (*p) {
                char *e = strchr(p, '\n'); size_t len = e ? (size_t)(e - p) : strlen(p);
                char line[1300]; if (len > 1299) len = 1299; memcpy(line, p, len); line[len] = 0;
                while (len && line[len - 1] == '\r') line[--len] = 0;
                p = e ? e + 1 : p + strlen(p);
                char *bar = strchr(line, '|'); if (!bar) continue; *bar = 0;
                wchar_t fw[300], uw[1100]; u8w(line, fw, 300); u8w(bar + 1, uw, 1100);
                if (safe_file_name(fw) && wcsncmp(uw, L"http", 4) == 0) sources_rewrite(NULL, fw, uw);
            }
            free(t);
        } else if (!_wcsicmp(fd.cFileName, MYFILE)) {                          /* mes chaines : fusion sans doublons */
            load_channels(); int before = nChans; parse_m3u(full, 0);
            for (int j = before; j < nChans; j++)
                for (int i = 0; i < before; i++) if (chans[i].file == 0 && !strcmp(chans[i].url, chans[j].url)) { chans[j].file = -1; break; }
            if (nChans > before) { save_own(-1); impCount++; }
        } else if (is_m3u_name(fd.cFileName)) {                                /* playlists : remplacees */
            wchar_t d[MAX_PATH]; dest_path(fd.cFileName, d); if (CopyFileW(full, d, FALSE)) impCount++;
        }
    } while (FindNextFileW(h, &fd));
    FindClose(h);
}

static void act_import_zip(void) {
    wchar_t zip[MAX_PATH] = L""; OPENFILENAMEW o; memset(&o, 0, sizeof o);
    o.lStructSize = sizeof o; o.hwndOwner = hMgr; o.lpstrFile = zip; o.nMaxFile = MAX_PATH;
    o.lpstrFilter = L"Archive ZIP\0*.zip\0"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetOpenFileNameW(&o)) return;
    wchar_t tmp[MAX_PATH], args[2000]; GetTempPathW(MAX_PATH, tmp);
    wchar_t dir[MAX_PATH]; _snwprintf(dir, MAX_PATH - 1, L"%slav_import_%lu", tmp, GetTickCount()); dir[MAX_PATH - 1] = 0;
    CreateDirectoryW(dir, NULL);
    _snwprintf(args, 1999, L"-x -f \"%s\" -C \"%s\"", zip, dir); args[1999] = 0;
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ec = run_tar(args);
    impCount = 0; if (ec == 0) import_walk(dir);
    SetCursor(old); rm_tree(dir);
    if (ec != 0) MessageBoxW(hMgr, L"Archive illisible (zip invalide, ou tar.exe de Windows absent).", L"IPTV", MB_ICONERROR);
    else { wchar_t m[260]; _snwprintf(m, 259, L"Import terminé : %d fichier(s) traité(s).\nLes playlists de même nom ont été remplacées ; vos chaînes ont été fusionnées.", impCount); m[259] = 0; MessageBoxW(hMgr, m, L"IPTV", MB_ICONINFORMATION); }
}

static LRESULT CALLBACK MgrProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_DRAWITEM: draw_btn((DRAWITEMSTRUCT *)lp, 0); return TRUE;
    case WM_NOTIFY: {
        NMHDR *nh = (NMHDR *)lp;
        if (nh->code == HDN_BEGINTRACKW || nh->code == HDN_DIVIDERDBLCLICKW) { NMHEADER *nmh = (NMHEADER *)lp; if (nmh->iItem == 4) return TRUE; return FALSE; }
        if (nh->hwndFrom == hLv && nh->code == NM_CUSTOMDRAW) {
            NMLVCUSTOMDRAW *cd = (NMLVCUSTOMDRAW *)lp;
            switch (cd->nmcd.dwDrawStage) {
            case CDDS_PREPAINT: return CDRF_NOTIFYITEMDRAW;
            case CDDS_ITEMPREPAINT: return CDRF_NOTIFYSUBITEMDRAW;
            case CDDS_ITEMPREPAINT | CDDS_SUBITEM: {
                int r = (int)cd->nmcd.dwItemSpec;
                if (cd->iSubItem == 4) {                                   /* indicateur : point colore, centre */
                    RECT rc; ListView_GetSubItemRect(hLv, r, 4, LVIR_BOUNDS, &rc); HDC dc = cd->nmcd.hdc;
                    int sel = (ListView_GetItemState(hLv, r, LVIS_SELECTED) & LVIS_SELECTED) != 0;
                    fill(dc, &rc, sel ? C_TROU : C_BG);
                    int st = (r >= 0 && r < 1024) ? rowState[r] : 0;
                    COLORREF col = st == 1 ? RGB(60, 200, 90) : st == 2 ? RGB(225, 85, 75) : C_DIM;
                    int cx = (rc.left + rc.right) / 2, cy = (rc.top + rc.bottom) / 2, rad = S(5);
                    SetDCBrushColor(dc, col); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN));
                    Ellipse(dc, cx - rad, cy - rad, cx + rad + 1, cy + rad + 1);
                    return CDRF_SKIPDEFAULT;
                }
                cd->clrTextBk = C_BG; cd->clrText = C_FG;
                return CDRF_NEWFONT; }
            }
            return CDRF_DODEFAULT;
        }
        if (nh->hwndFrom == hLv) {
            if (nh->code == LVN_ITEMCHANGED) mgr_buttons();
            else if (nh->code == NM_DBLCLK) {
                int pl, idx; if (mgr_get(&pl, &idx)) { if (!pl) { play_channel(idx); mgrDone = 1; } else act_edit(), mgr_fill(), mgr_buttons(); }
            }
        }
        return 0; }
    case WM_COMMAND:
        switch (LOWORD(wp)) {
        case M_ADDC: act_add_channel(); mgr_fill(); mgr_buttons(); break;
        case M_ADDP: act_add_playlist(); mgr_fill(); mgr_buttons(); break;
        case M_IMP: act_import(); mgr_fill(); mgr_buttons(); break;
        case M_EDIT: act_edit(); mgr_fill(); mgr_buttons(); break;
        case M_REPL: act_replace(); mgr_fill(); mgr_buttons(); break;
        case M_REF: act_refresh(); mgr_fill(); mgr_buttons(); break;
        case M_DEL: act_delete(); mgr_fill(); mgr_buttons(); break;
        case M_EXP: act_export(); break;
        case M_IMPZ: act_import_zip(); mgr_fill(); mgr_buttons(); break;
        case M_DIR: ShellExecuteW(NULL, L"open", iptvDir, NULL, NULL, SW_SHOWNORMAL); break;
        case IDCANCEL: mgrDone = 1; break;
        }
        return 0;
    case WM_MGR_STATE: if (wp < 1024) { rowState[wp] = (int)lp; ListView_RedrawItems(hLv, (int)wp, (int)wp); } return 0;
    case WM_CLOSE: mgrDone = 1; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

static void manage_window(void) {
    static int reg = 0; iptv_init_dir();
    if (!reg) {
        if (!brDlg) { brDlg = CreateSolidBrush(C_BAR); brEdit = CreateSolidBrush(C_BG); }
        WNDCLASSW wc; memset(&wc, 0, sizeof wc);
        wc.lpfnWndProc = MgrProc; wc.hInstance = hInst; wc.lpszClassName = L"LavMgr";
        wc.hbrBackground = brDlg; wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hIcon = LoadIconW(hInst, MAKEINTRESOURCEW(1));
        RegisterClassW(&wc); reg = 1;
    }
    mgrDone = 0;
    hMgr = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LavMgr", L"Gestion des listes IPTV", WS_POPUP | WS_CAPTION | WS_SYSMENU | WS_CLIPCHILDREN,
                           0, 0, 300, 200, hMain, NULL, hInst, NULL);
    int cw = S(860), ch = S(460);
    RECT wr, cr; GetWindowRect(hMgr, &wr); GetClientRect(hMgr, &cr);
    int ow = (wr.right - wr.left) - cr.right + cw, oh = (wr.bottom - wr.top) - cr.bottom + ch;
    RECT mr; GetWindowRect(hMain, &mr);
    SetWindowPos(hMgr, NULL, mr.left + ((mr.right - mr.left) - ow) / 2, mr.top + ((mr.bottom - mr.top) - oh) / 2, ow, oh, SWP_NOZORDER);
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute");
               if (f) { f(hMgr, 20, &dark, sizeof dark); f(hMgr, 19, &dark, sizeof dark); } }

    hLv = CreateWindowExW(0, WC_LISTVIEWW, NULL, WS_CHILD | WS_VISIBLE | WS_TABSTOP | LVS_REPORT | LVS_SINGLESEL | LVS_SHOWSELALWAYS,
                          S(12), S(12), S(660), ch - S(24), hMgr, (HMENU)200, hInst, NULL);
    SendMessage(hLv, WM_SETFONT, (WPARAM)fUI, 1);
    ListView_SetExtendedListViewStyle(hLv, LVS_EX_FULLROWSELECT | LVS_EX_DOUBLEBUFFER);
    ListView_SetBkColor(hLv, C_BG); ListView_SetTextBkColor(hLv, C_BG); ListView_SetTextColor(hLv, C_FG);
    HMODULE ux = LoadLibraryW(L"uxtheme.dll");
    if (ux) { HRESULT (WINAPI *st)(HWND, LPCWSTR, LPCWSTR) = (void *)GetProcAddress(ux, "SetWindowTheme");
              if (st) { st(hLv, L"DarkMode_Explorer", NULL); st(ListView_GetHeader(hLv), L"DarkMode_ItemsView", NULL); } }
    const wchar_t *cols[5] = { L"Nom", L"Type", L"Chaînes", L"Adresse / source", L"État" };
    int cwid[5] = { S(190), S(66), S(66), 0, S(40) };                     /* État : largeur fixe, calee sur le point */
    { RECT lr; GetClientRect(hLv, &lr); cwid[3] = lr.right - GetSystemMetrics(SM_CXVSCROLL) - cwid[0] - cwid[1] - cwid[2] - cwid[4]; if (cwid[3] < S(100)) cwid[3] = S(100); }
    for (int i = 0; i < 5; i++) {
        LVCOLUMN c; memset(&c, 0, sizeof c); c.mask = LVCF_TEXT | LVCF_WIDTH | (i == 4 ? LVCF_FMT : 0); c.pszText = (LPWSTR)cols[i]; c.cx = cwid[i];
        if (i == 4) c.fmt = LVCFMT_CENTER;
        ListView_InsertColumn(hLv, i, &c);
    }
    const wchar_t *lab[10] = { L"Ajouter une chaîne…", L"Ajouter une playlist…", L"Importer un fichier…", L"Modifier…",
                               L"Remplacer…", L"Actualiser", L"Supprimer", L"Exporter (zip)…", L"Importer (zip)…", L"Ouvrir le dossier" };
    int y = S(12);
    for (int i = 0; i < 10; i++) {
        mgrBtn[i] = CreateWindowExW(0, L"BUTTON", lab[i], WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(686), y, S(160), S(30), hMgr, (HMENU)(INT_PTR)(301 + i), hInst, NULL);
        y += S(30) + S((i == 2 || i == 6) ? 18 : 6);
    }
    CreateWindowExW(0, L"BUTTON", L"Fermer", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(686), ch - S(12) - S(30), S(160), S(30), hMgr, (HMENU)IDCANCEL, hInst, NULL);

    mgr_fill(); mgr_buttons();
    int prevMenu = menuOpen; menuOpen = 1; EnableWindow(hMain, FALSE);
    ShowWindow(hMgr, SW_SHOW); SetForegroundWindow(hMgr); SetFocus(hLv);
    MSG msg;
    while (!mgrDone) {
        int r = GetMessage(&msg, NULL, 0, 0);
        if (r <= 0) { if (r == 0) PostQuitMessage((int)msg.wParam); break; }
        if (!IsDialogMessage(hMgr, &msg)) { TranslateMessage(&msg); DispatchMessage(&msg); }
    }
    { int own = 0; for (int i = 0; i < nChans; i++) if (chans[i].file == 0) own++;
      if (own) save_own(-1); }                       /* fermeture (bouton Fermer, croix ou Echap) : toute la liste est reecrite sur disque */
    EnableWindow(hMain, TRUE); DestroyWindow(hMgr); hMgr = NULL; menuOpen = prevMenu;
    SetForegroundWindow(hMain);
    /* la selection langue / categorie doit rester valide apres les modifications */
    load_channels();
    { int ok = !selList[0]; for (int f = 0; f < nFiles; f++) if (!_wcsicmp(fileNames[f], selList)) ok = 1; if (!ok) { selList[0] = 0; selLang[0] = 0; selCat[0] = 0; } }
    build_cats();
    { int ok = !selLang[0]; for (int k = 0; k < nLangs; k++) if (!wcscmp(langs[k], selLang)) ok = 1; if (!ok) { selLang[0] = 0; selCat[0] = 0; } }
    build_cats();
    { int ok = !selCat[0]; for (int k = 0; k < nCats; k++) if (!wcscmp(cats[k], selCat)) ok = 1; if (!ok) selCat[0] = 0; }
    save_sel(); inval();
}


/* ================= parametres : versions et mise a jour ================= */
#define LAV_VERSION L"1.1"
#define WM_SET_ONLINE (WM_APP + 10)
#define WM_SET_UPD    (WM_APP + 11)
static HWND hSet, hsVal[5], hsStatus, hsUpd, hsRestart;
static int setDone, onlineState;                       /* 0 recherche, 1 ok, 2 echec */
static wchar_t onlineTag[64], onlineName[200], onlineHash[24], updMsg[240];
static char onlineUrl[700];
static volatile int updRunning, updOk;
static COLORREF statusClr;

static int json_str(const char *j, const char *key, char *out, int n) {
    char k[64]; snprintf(k, sizeof k, "\"%s\"", key); const char *p = strstr(j, k); if (!p) return 0;
    p += strlen(k); while (*p && *p != '"') p++; if (*p != '"') return 0; p++;
    int i = 0; while (*p && *p != '"' && i < n - 1) out[i++] = *p++; out[i] = 0; return 1;
}
static void exe_dir(wchar_t *d) { GetModuleFileNameW(NULL, d, MAX_PATH); wchar_t *p = wcsrchr(d, L'\\'); if (p) *p = 0; }
static void get_prop(const char *name, wchar_t *out, int n) {
    char *v = p_get_property_string(mpv, name);
    if (v) { u8w(v, out, n); p_free(v); } else wcsncpy(out, L"inconnue", n);
}

static DWORD WINAPI fetch_thread(LPVOID a) {
    HWND h = (HWND)a; wchar_t tmp[MAX_PATH], api[] = L"https://api.github.com/repos/shinchiro/mpv-winbuild-cmake/releases/latest";
    GetTempPathW(MAX_PATH, tmp); wcscat(tmp, L"lav_release.json");
    onlineState = 2; DeleteUrlCacheEntryW(api);
    if (SUCCEEDED(URLDownloadToFileW(NULL, api, tmp, 0, NULL))) {
        char *j = read_all(tmp);
        if (j) {
            char tag[64];
            if (json_str(j, "tag_name", tag, 64)) {
                u8w(tag, onlineTag, 64);
                const char *p = j;
                while ((p = strstr(p, "\"browser_download_url\""))) {
                    char url[700];
                    if (json_str(p, "browser_download_url", url, 700)) {
                        const char *b = strstr(url, "/mpv-dev-x86_64-");
                        if (b && isdigit((unsigned char)b[16])) {
                            strcpy(onlineUrl, url); u8w(b + 1, onlineName, 200);
                            const char *g = strstr(b, "-git-"); onlineHash[0] = 0;
                            if (g) { char hs[8]; strncpy(hs, g + 5, 7); hs[7] = 0; u8w(hs, onlineHash, 24); }
                            onlineState = 1; break;
                        }
                    }
                    p += 21;
                }
            }
            free(j);
        }
        DeleteFileW(tmp);
    }
    if (IsWindow(h)) PostMessage(h, WM_SET_ONLINE, 0, 0);
    return 0;
}

static int update_available(void) {
    if (onlineState != 1) return 0;
    wchar_t d[MAX_PATH], vf[MAX_PATH]; exe_dir(d); _snwprintf(vf, MAX_PATH - 1, L"%s\\libmpv.version", d); vf[MAX_PATH - 1] = 0;
    char *t = read_all(vf);
    if (t) { wchar_t w[64]; u8w(t, w, 64); free(t); wchar_t *e = w + wcslen(w); while (e > w && (e[-1] == L'\r' || e[-1] == L'\n' || e[-1] == L' ')) *--e = 0; if (!wcscmp(w, onlineTag)) return 0; }
    wchar_t inst[256]; get_prop("mpv-version", inst, 256);
    if (onlineHash[0] && wcsstr(inst, onlineHash)) return 0;
    return 1;
}

static int find_file(const wchar_t *dir, const wchar_t *name, wchar_t *out) {
    wchar_t pat[MAX_PATH]; _snwprintf(pat, MAX_PATH - 1, L"%s\\*", dir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd); if (h == INVALID_HANDLE_VALUE) return 0; int found = 0;
    do {
        if (!wcscmp(fd.cFileName, L".") || !wcscmp(fd.cFileName, L"..")) continue;
        wchar_t full[MAX_PATH]; _snwprintf(full, MAX_PATH - 1, L"%s\\%s", dir, fd.cFileName); full[MAX_PATH - 1] = 0;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) { if (find_file(full, name, out)) { found = 1; break; } }
        else if (!_wcsicmp(fd.cFileName, name)) { wcscpy(out, full); found = 1; break; }
    } while (FindNextFileW(h, &fd));
    FindClose(h); return found;
}

static void upd_status(HWND h, const wchar_t *m) { wcsncpy(updMsg, m, 239); updMsg[239] = 0; if (IsWindow(h)) PostMessage(h, WM_SET_UPD, 0, 0); }

static DWORD WINAPI update_thread(LPVOID a) {
    HWND h = (HWND)a; updRunning = 1; updOk = 0;
    wchar_t dir[MAX_PATH], ex[MAX_PATH], arc[MAX_PATH], seven[MAX_PATH] = L"", url[800], newdll[MAX_PATH] = L"";
    GetTempPathW(MAX_PATH, dir); wcscat(dir, L"lav_update\\"); CreateDirectoryW(dir, NULL);
    _snwprintf(ex, MAX_PATH - 1, L"%sx", dir); ex[MAX_PATH - 1] = 0; CreateDirectoryW(ex, NULL);
    _snwprintf(arc, MAX_PATH - 1, L"%sasset.7z", dir); arc[MAX_PATH - 1] = 0;
    u8w(onlineUrl, url, 800);
    upd_status(h, L"Téléchargement de libmpv…"); DeleteUrlCacheEntryW(url);
    if (FAILED(URLDownloadToFileW(NULL, url, arc, 0, NULL))) { upd_status(h, L"Échec du téléchargement."); goto done; }
    {
        const wchar_t *cand[2] = { L"%ProgramFiles%\\7-Zip\\7z.exe", L"%ProgramFiles(x86)%\\7-Zip\\7z.exe" };
        for (int i = 0; i < 2 && !seven[0]; i++) { wchar_t e[MAX_PATH]; ExpandEnvironmentStringsW(cand[i], e, MAX_PATH); if (GetFileAttributesW(e) != INVALID_FILE_ATTRIBUTES) wcscpy(seven, e); }
        if (!seven[0]) {
            _snwprintf(seven, MAX_PATH - 1, L"%s7zr.exe", dir); seven[MAX_PATH - 1] = 0;
            upd_status(h, L"Téléchargement de l'extracteur 7-Zip…");
            if (FAILED(URLDownloadToFileW(NULL, L"https://www.7-zip.org/a/7zr.exe", seven, 0, NULL))) { upd_status(h, L"Extracteur 7-Zip introuvable (hors ligne ?)."); goto done; }
        }
    }
    upd_status(h, L"Extraction…");
    {
        wchar_t cmdl[2400]; _snwprintf(cmdl, 2399, L"\"%s\" x -y \"-o%s\" \"%s\" *.dll -r", seven, ex, arc); cmdl[2399] = 0;
        STARTUPINFOW si; memset(&si, 0, sizeof si); si.cb = sizeof si; PROCESS_INFORMATION pi;
        if (!CreateProcessW(NULL, cmdl, NULL, NULL, FALSE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi)) { upd_status(h, L"Extraction impossible."); goto done; }
        WaitForSingleObject(pi.hProcess, 180000); CloseHandle(pi.hThread); CloseHandle(pi.hProcess);
    }
    if (!find_file(ex, L"libmpv-2.dll", newdll) && !find_file(ex, L"mpv-2.dll", newdll)) { upd_status(h, L"DLL introuvable dans l'archive."); goto done; }
    {
        WIN32_FILE_ATTRIBUTE_DATA fa; if (!GetFileAttributesExW(newdll, GetFileExInfoStandard, &fa) || fa.nFileSizeLow < 1000000) { upd_status(h, L"Fichier téléchargé invalide."); goto done; }
        upd_status(h, L"Installation…");
        wchar_t old[MAX_PATH]; _snwprintf(old, MAX_PATH - 1, L"%s.old", gDllPath); old[MAX_PATH - 1] = 0;
        DeleteFileW(old);
        int had = GetFileAttributesW(gDllPath) != INVALID_FILE_ATTRIBUTES;
        if (had && !MoveFileExW(gDllPath, old, MOVEFILE_REPLACE_EXISTING)) { upd_status(h, L"Impossible de remplacer la DLL (droits d'\u00e9criture ?)."); goto done; }
        if (!CopyFileW(newdll, gDllPath, FALSE)) { if (had) MoveFileExW(old, gDllPath, MOVEFILE_REPLACE_EXISTING); upd_status(h, L"Copie de la DLL impossible (dossier en \u00e9criture seule ?)."); goto done; }
        wchar_t d[MAX_PATH], vf[MAX_PATH]; exe_dir(d); _snwprintf(vf, MAX_PATH - 1, L"%s\\libmpv.version", d); vf[MAX_PATH - 1] = 0;
        char t8[80]; w8(onlineTag, t8, sizeof t8);
        HANDLE f = CreateFileW(vf, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
        if (f != INVALID_HANDLE_VALUE) { DWORD w; WriteFile(f, t8, (DWORD)strlen(t8), &w, NULL); CloseHandle(f); }
        updOk = 1; upd_status(h, L"Mise à jour installée. Redémarrez le lecteur pour l'appliquer.");
    }
done:
    updRunning = 0; if (IsWindow(h)) PostMessage(h, WM_SET_UPD, 0, 0);
    return 0;
}


/* ================= bibliotheque FFmpeg (dossier codec) ================= */
#define WM_SET_FFONLINE (WM_APP + 12)
#define WM_SET_FFUPD    (WM_APP + 13)
#define FF_URL_GYAN     L"https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
static wchar_t ffOnlineVer[64], ffUrl2[300], ffInstVer[160], ffMsg[240];
static int ffOnlineState;                               /* 0 recherche, 1 ok, 2 echec */
static volatile int ffUpdRunning, ffUpdOk, ffAbort;

static void codec_dir(wchar_t *d) { exe_dir(d); wcscat(d, L"\\codec"); }
static void ff_path(wchar_t *p) { codec_dir(p); wcscat(p, L"\\ffmpeg.exe"); }
static int ff_present(void) { wchar_t p[MAX_PATH]; ff_path(p); return GetFileAttributesW(p) != INVALID_FILE_ATTRIBUTES; }
static void ff_status(HWND h, const wchar_t *m) { wcsncpy(ffMsg, m, 239); ffMsg[239] = 0; if (IsWindow(h)) PostMessage(h, WM_SET_FFUPD, 0, 0); }

/* lance une commande et recupere sa sortie (stdout + stderr) */
static int run_capture(const wchar_t *cmdline, char *out, int n, DWORD timeout) {
    SECURITY_ATTRIBUTES sa = { sizeof sa, NULL, TRUE }; HANDLE r, w; out[0] = 0;
    if (!CreatePipe(&r, &w, &sa, 0)) return -1;
    SetHandleInformation(r, HANDLE_FLAG_INHERIT, 0);
    STARTUPINFOW si; memset(&si, 0, sizeof si); si.cb = sizeof si; si.dwFlags = STARTF_USESTDHANDLES; si.hStdOutput = w; si.hStdError = w;
    wchar_t cl[1200]; wcsncpy(cl, cmdline, 1199); cl[1199] = 0; PROCESS_INFORMATION pi;
    if (!CreateProcessW(NULL, cl, NULL, NULL, TRUE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi)) { CloseHandle(r); CloseHandle(w); return -1; }
    CloseHandle(w);
    int len = 0; DWORD got;
    while (len < n - 1 && ReadFile(r, out + len, n - 1 - len, &got, NULL) && got) len += (int)got;
    out[len] = 0; CloseHandle(r);
    if (WaitForSingleObject(pi.hProcess, timeout) != WAIT_OBJECT_0) TerminateProcess(pi.hProcess, 1);
    DWORD ec = 1; GetExitCodeProcess(pi.hProcess, &ec); CloseHandle(pi.hThread); CloseHandle(pi.hProcess); return (int)ec;
}

static void ff_installed_version(wchar_t *out, int n) {
    wchar_t p[MAX_PATH], cl[MAX_PATH + 40]; char b[1500];
    if (!ff_present()) { wcsncpy(out, L"non installé", n); out[n - 1] = 0; return; }
    ff_path(p); _snwprintf(cl, MAX_PATH + 39, L"\"%s\" -version", p); cl[MAX_PATH + 39] = 0;
    run_capture(cl, b, sizeof b, 8000);
    char *v = strstr(b, "version ");
    if (!v) { wcsncpy(out, L"version inconnue", n); out[n - 1] = 0; return; }
    v += 8; char tok[160]; int i = 0;
    while (*v && *v != ' ' && *v != '\r' && *v != '\n' && i < 159) tok[i++] = *v++;
    tok[i] = 0; u8w(tok, out, n);
}

static int http_get_text(const char *url, char *out, int n) {
    int len = 0; out[0] = 0;
    HINTERNET hi = InternetOpenA("Mozilla/5.0 LecteurAV", INTERNET_OPEN_TYPE_PRECONFIG, NULL, NULL, 0); if (!hi) return 0;
    DWORD to = 10000; InternetSetOptionA(hi, INTERNET_OPTION_CONNECT_TIMEOUT, &to, sizeof to); InternetSetOptionA(hi, INTERNET_OPTION_RECEIVE_TIMEOUT, &to, sizeof to);
    HINTERNET hu = InternetOpenUrlA(hi, url, "Accept: */*\r\n", (DWORD)-1, INTERNET_FLAG_RELOAD | INTERNET_FLAG_NO_CACHE_WRITE, 0);
    if (hu) {
        DWORD code = 0, cl = sizeof code; HttpQueryInfoA(hu, HTTP_QUERY_STATUS_CODE | HTTP_QUERY_FLAG_NUMBER, &code, &cl, NULL);
        if (code == 200) { DWORD got; while (len < n - 1 && InternetReadFile(hu, out + len, n - 1 - len, &got) && got) len += (int)got; }
        InternetCloseHandle(hu);
    }
    InternetCloseHandle(hi);
    if (len > 0) out[len] = 0;
    return len > 0;
}

/* telechargement avec progression (wininet) */
static int http_download(const wchar_t *urlw, const wchar_t *dest, HWND h, const wchar_t *label) {
    char url[700]; w8(urlw, url, sizeof url); int ok = 0;
    HINTERNET hi = InternetOpenA("Mozilla/5.0 LecteurAV", INTERNET_OPEN_TYPE_PRECONFIG, NULL, NULL, 0);
    if (hi) { DWORD to = 20000; InternetSetOptionA(hi, INTERNET_OPTION_CONNECT_TIMEOUT, &to, sizeof to); InternetSetOptionA(hi, INTERNET_OPTION_RECEIVE_TIMEOUT, &to, sizeof to); }
    HINTERNET hu = hi ? InternetOpenUrlA(hi, url, NULL, 0, INTERNET_FLAG_RELOAD | INTERNET_FLAG_NO_CACHE_WRITE | INTERNET_FLAG_KEEP_CONNECTION, 0) : NULL;
    if (hu) {
        DWORD code = 0, cl = sizeof code; HttpQueryInfoA(hu, HTTP_QUERY_STATUS_CODE | HTTP_QUERY_FLAG_NUMBER, &code, &cl, NULL);
        DWORD tl = 0, tll = sizeof tl; HttpQueryInfoA(hu, HTTP_QUERY_CONTENT_LENGTH | HTTP_QUERY_FLAG_NUMBER, &tl, &tll, NULL);
        if (code == 200) {
            HANDLE f = CreateFileW(dest, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
            if (f != INVALID_HANDLE_VALUE) {
                static BYTE buf[65536]; DWORD got, last = 0; unsigned long long tot = 0; ok = 1;
                for (;;) {
                    if (ffAbort) { ok = 0; break; }
                    if (!InternetReadFile(hu, buf, sizeof buf, &got)) { ok = 0; break; }
                    if (!got) break;
                    DWORD w; if (!WriteFile(f, buf, got, &w, NULL) || w != got) { ok = 0; break; }
                    tot += got;
                    if (GetTickCount() - last > 300) {
                        last = GetTickCount(); wchar_t m[200];
                        if (tl) _snwprintf(m, 199, L"%s   %d %%   (%.0f / %.0f Mo)", label, (int)(tot * 100 / tl), tot / 1048576.0, tl / 1048576.0);
                        else _snwprintf(m, 199, L"%s   %.0f Mo", label, tot / 1048576.0);
                        m[199] = 0; ff_status(h, m);
                    }
                }
                CloseHandle(f);
                if (ok && tl && tot < tl) ok = 0;
            }
        }
        InternetCloseHandle(hu);
    }
    if (hi) InternetCloseHandle(hi);
    if (!ok) DeleteFileW(dest);
    return ok;
}

static DWORD WINAPI ff_fetch_thread(LPVOID a) {
    HWND h = (HWND)a; char b[16384], v[64] = ""; ffOnlineState = 2; ffOnlineVer[0] = 0; ffUrl2[0] = 0;
    ff_installed_version(ffInstVer, 160);
    if (http_get_text("https://www.gyan.dev/ffmpeg/builds/release-version", b, 64)) {
        int i = 0; for (const char *p = b; *p && i < 31 && (isdigit((unsigned char)*p) || *p == '.'); p++) v[i++] = *p; v[i] = 0;
    }
    if (!v[0] && http_get_text("https://api.github.com/repos/GyanD/codexffmpeg/releases/latest", b, sizeof b)) json_str(b, "tag_name", v, 32);
    if (v[0] && isdigit((unsigned char)v[0])) {
        u8w(v, ffOnlineVer, 64);
        _snwprintf(ffUrl2, 299, L"https://github.com/GyanD/codexffmpeg/releases/download/%s/ffmpeg-%s-essentials_build.zip", ffOnlineVer, ffOnlineVer); ffUrl2[299] = 0;
        ffOnlineState = 1;
    }
    if (IsWindow(h)) PostMessage(h, WM_SET_FFONLINE, 0, 0);
    return 0;
}

static int ff_update_available(void) {
    if (ffOnlineState != 1) return 0;
    if (!ff_present()) return 1;
    size_t l = wcslen(ffOnlineVer);
    if (!wcsncmp(ffInstVer, ffOnlineVer, l) && (ffInstVer[l] == 0 || ffInstVer[l] == L'-')) return 0;
    return 1;
}

/* telecharge, extrait (tar.exe de Windows) et installe ffmpeg.exe dans le dossier codec */
static int ff_install(HWND h) {
    wchar_t cd[MAX_PATH], tmp[MAX_PATH], zip[MAX_PATH], ex[MAX_PATH], dst[MAX_PATH], old[MAX_PATH], newexe[MAX_PATH] = L"", args[2600]; int ok = 0;
    codec_dir(cd); CreateDirectoryW(cd, NULL);
    GetTempPathW(MAX_PATH, tmp); wcscat(tmp, L"lav_ffmpeg"); rm_tree(tmp); CreateDirectoryW(tmp, NULL);
    _snwprintf(zip, MAX_PATH - 1, L"%s\\ffmpeg.zip", tmp); zip[MAX_PATH - 1] = 0;
    _snwprintf(ex, MAX_PATH - 1, L"%s\\x", tmp); ex[MAX_PATH - 1] = 0; CreateDirectoryW(ex, NULL);
    ff_status(h, L"Téléchargement de FFmpeg…");
    if (!http_download(FF_URL_GYAN, zip, h, L"Téléchargement de FFmpeg") && !(ffUrl2[0] && http_download(ffUrl2, zip, h, L"Téléchargement de FFmpeg"))) {
        ff_status(h, L"Échec du téléchargement de FFmpeg (hors ligne ?)."); goto done;
    }
    ff_status(h, L"Extraction de FFmpeg…");
    _snwprintf(args, 2599, L"-x -f \"%s\" -C \"%s\" \"*/bin/ffmpeg.exe\"", zip, ex); args[2599] = 0; run_tar(args);
    if (!find_file(ex, L"ffmpeg.exe", newexe)) {                       /* repli : extraction complete */
        _snwprintf(args, 2599, L"-x -f \"%s\" -C \"%s\"", zip, ex); args[2599] = 0; run_tar(args);
        if (!find_file(ex, L"ffmpeg.exe", newexe)) { ff_status(h, L"ffmpeg.exe introuvable dans l'archive (tar.exe requis)."); goto done; }
    }
    {
        WIN32_FILE_ATTRIBUTE_DATA fa; char b[600]; wchar_t cl[MAX_PATH + 40];
        if (!GetFileAttributesExW(newexe, GetFileExInfoStandard, &fa) || fa.nFileSizeLow < 10000000) { ff_status(h, L"Fichier FFmpeg invalide."); goto done; }
        _snwprintf(cl, MAX_PATH + 39, L"\"%s\" -version", newexe); cl[MAX_PATH + 39] = 0;
        run_capture(cl, b, sizeof b, 15000);
        if (!strstr(b, "ffmpeg version")) { ff_status(h, L"Le FFmpeg téléchargé ne démarre pas (x64 requis)."); goto done; }
    }
    ff_status(h, L"Installation de FFmpeg…");
    ff_path(dst); _snwprintf(old, MAX_PATH - 1, L"%s.old", dst); old[MAX_PATH - 1] = 0; DeleteFileW(old);
    {
        int had = GetFileAttributesW(dst) != INVALID_FILE_ATTRIBUTES;
        if (had && !MoveFileExW(dst, old, MOVEFILE_REPLACE_EXISTING)) { ff_status(h, L"Impossible de remplacer ffmpeg.exe (capture en cours ?)."); goto done; }
        if (!CopyFileW(newexe, dst, FALSE)) { if (had) MoveFileExW(old, dst, MOVEFILE_REPLACE_EXISTING); ff_status(h, L"Copie impossible (dossier codec en écriture seule ?)."); goto done; }
        DeleteFileW(old);
    }
    ff_installed_version(ffInstVer, 160);
    ok = 1; ff_status(h, L"FFmpeg installé.");
done:
    rm_tree(tmp);
    return ok;
}

static DWORD WINAPI ff_update_thread(LPVOID a) {
    HWND h = (HWND)a; ffUpdRunning = 1; ffUpdOk = 0; ffAbort = 0;
    ffUpdOk = ff_install(h);
    ffUpdRunning = 0; if (IsWindow(h)) PostMessage(h, WM_SET_FFUPD, 0, 0);
    return 0;
}

static COLORREF ffStatusClr; static HWND hsFf[3], hsFfStatus, hsFfUpd;
static void set_ff_refresh(void) {
    int pres = ff_present();
    if (ffOnlineState == 0) { SetWindowTextW(hsFf[2], L"Recherche en ligne\u2026"); ffStatusClr = C_DIM; SetWindowTextW(hsFfStatus, L""); }
    else if (ffOnlineState == 2) { SetWindowTextW(hsFf[2], L"Indisponible (hors ligne ?)"); ffStatusClr = C_DIM;
        SetWindowTextW(hsFfStatus, pres ? L"Impossible de v\u00e9rifier la derni\u00e8re version." : L"FFmpeg n'est pas install\u00e9 et la v\u00e9rification en ligne a \u00e9chou\u00e9."); }
    else {
        SetWindowTextW(hsFf[2], ffOnlineVer);
        if (!pres) { ffStatusClr = C_ACC; SetWindowTextW(hsFfStatus, L"FFmpeg n'est pas install\u00e9 \u2014 cliquez sur l'ic\u00f4ne \u2193 pour l'installer."); }
        else if (ff_update_available()) { ffStatusClr = C_ACC; SetWindowTextW(hsFfStatus, L"Mise \u00e0 jour disponible \u2014 cliquez sur l'ic\u00f4ne \u2193 pour recharger FFmpeg."); }
        else { ffStatusClr = RGB(60, 200, 90); SetWindowTextW(hsFfStatus, L"\u25cf  FFmpeg est \u00e0 jour."); }
    }
    if (ffUpdRunning || ffMsg[0]) { SetWindowTextW(hsFfStatus, ffMsg); ffStatusClr = ffUpdOk ? RGB(60, 200, 90) : C_ACC; }
    if (capRunning) { SetWindowTextW(hsFfStatus, L"Arr\u00eatez l'enregistrement avant de mettre \u00e0 jour FFmpeg."); ffStatusClr = C_ACC; }
    SetWindowTextW(hsFf[1], ffInstVer[0] ? ffInstVer : L"\u2026");
    EnableWindow(hsFfUpd, ffOnlineState == 1 && !ffUpdRunning && !capRunning && (!pres || ff_update_available()));
    InvalidateRect(hSet, NULL, TRUE);
}

static void set_refresh(void) {
    wchar_t v[300];
    if (onlineState == 0) { SetWindowTextW(hsVal[4], L"Recherche en ligne…"); statusClr = C_DIM; SetWindowTextW(hsStatus, L""); }
    else if (onlineState == 2) { SetWindowTextW(hsVal[4], L"Indisponible (hors ligne ?)"); statusClr = C_DIM; SetWindowTextW(hsStatus, L"Impossible de vérifier la dernière version."); }
    else {
        _snwprintf(v, 299, L"%s   ·   %s", onlineTag, onlineName); v[299] = 0; SetWindowTextW(hsVal[4], v);
        if (update_available()) { statusClr = C_ACC; SetWindowTextW(hsStatus, L"Mise à jour disponible — cliquez sur l'icône ↓ pour l'installer."); }
        else { statusClr = RGB(60, 200, 90); SetWindowTextW(hsStatus, L"●  libmpv est à jour."); }
    }
    if (updRunning || updMsg[0]) { SetWindowTextW(hsStatus, updMsg); statusClr = updOk ? RGB(60, 200, 90) : C_ACC; }
    EnableWindow(hsUpd, onlineState == 1 && !updRunning && !updOk && update_available());
    ShowWindow(hsRestart, updOk ? SW_SHOW : SW_HIDE);
    InvalidateRect(hSet, NULL, TRUE);
}


/* ---------- mise a jour de l'application depuis un fichier zip (listes et configuration conservees) ---------- */
static int find_file_rec(const wchar_t *dir, const wchar_t *name, wchar_t *out, int depth) {
    wchar_t pat[MAX_PATH]; _snwprintf(pat, MAX_PATH - 1, L"%s\\*", dir); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd); if (h == INVALID_HANDLE_VALUE) return 0; int found = 0;
    do {
        if (!wcscmp(fd.cFileName, L".") || !wcscmp(fd.cFileName, L"..")) continue;
        wchar_t f[MAX_PATH]; _snwprintf(f, MAX_PATH - 1, L"%s\\%s", dir, fd.cFileName); f[MAX_PATH - 1] = 0;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) { if (depth < 4 && _wcsicmp(fd.cFileName, L"source") && find_file_rec(f, name, out, depth + 1)) { found = 1; break; } }
        else if (!_wcsicmp(fd.cFileName, name)) { wcscpy(out, f); found = 1; break; }
    } while (FindNextFileW(h, &fd));
    FindClose(h); return found;
}
static void copy_missing(const wchar_t *src, const wchar_t *dst) {       /* copie uniquement ce qui n'existe pas encore */
    wchar_t pat[MAX_PATH]; _snwprintf(pat, MAX_PATH - 1, L"%s\\*", src); pat[MAX_PATH - 1] = 0;
    WIN32_FIND_DATAW fd; HANDLE h = FindFirstFileW(pat, &fd); if (h == INVALID_HANDLE_VALUE) return;
    CreateDirectoryW(dst, NULL);
    do {
        if (!wcscmp(fd.cFileName, L".") || !wcscmp(fd.cFileName, L"..")) continue;
        wchar_t a[MAX_PATH], b[MAX_PATH]; _snwprintf(a, MAX_PATH - 1, L"%s\\%s", src, fd.cFileName); _snwprintf(b, MAX_PATH - 1, L"%s\\%s", dst, fd.cFileName); a[MAX_PATH - 1] = b[MAX_PATH - 1] = 0;
        if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) copy_missing(a, b);
        else if (GetFileAttributesW(b) == INVALID_FILE_ATTRIBUTES) CopyFileW(a, b, TRUE);
    } while (FindNextFileW(h, &fd));
    FindClose(h);
}
static int act_update_app(HWND owner) {
    wchar_t zip[MAX_PATH] = L""; OPENFILENAMEW o; memset(&o, 0, sizeof o);
    o.lStructSize = sizeof o; o.hwndOwner = owner; o.lpstrFile = zip; o.nMaxFile = MAX_PATH; o.lpstrTitle = L"Choisir le zip de la nouvelle version";
    o.lpstrFilter = L"Archive ZIP\0*.zip\0"; o.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST | OFN_EXPLORER;
    if (!GetOpenFileNameW(&o)) return 0;
    wchar_t tmp[MAX_PATH], dir[MAX_PATH], args[2000], newExe[MAX_PATH] = L"";
    GetTempPathW(MAX_PATH, tmp); _snwprintf(dir, MAX_PATH - 1, L"%slav_upd_%lu", tmp, GetTickCount()); dir[MAX_PATH - 1] = 0;
    CreateDirectoryW(dir, NULL);
    _snwprintf(args, 1999, L"-x -f \"%s\" -C \"%s\"", zip, dir); args[1999] = 0;
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ec = run_tar(args); SetCursor(old);
    if (ec != 0) { rm_tree(dir); MessageBoxW(owner, L"Archive illisible (zip invalide, ou tar.exe de Windows absent).", L"Mise à jour", MB_ICONERROR); return 0; }
    if (!find_file_rec(dir, L"lecteur.exe", newExe, 0)) { rm_tree(dir); MessageBoxW(owner, L"Ce zip ne contient pas de fichier lecteur.exe.", L"Mise à jour", MB_ICONERROR); return 0; }
    WIN32_FILE_ATTRIBUTE_DATA fa; unsigned char mz[2] = { 0, 0 }; DWORD rd = 0; HANDLE hf = CreateFileW(newExe, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (hf != INVALID_HANDLE_VALUE) { ReadFile(hf, mz, 2, &rd, NULL); CloseHandle(hf); }
    if (!GetFileAttributesExW(newExe, GetFileExInfoStandard, &fa) || fa.nFileSizeLow < 100000 || mz[0] != 'M' || mz[1] != 'Z') {
        rm_tree(dir); MessageBoxW(owner, L"Le fichier lecteur.exe du zip n'est pas valide.", L"Mise à jour", MB_ICONERROR); return 0; }
    if (MessageBoxW(owner, L"Installer la nouvelle version du lecteur ?\n\nVos listes IPTV, vos chaînes et la configuration sont conservées.\nL'application redémarrera.", L"Mise à jour", MB_YESNO | MB_ICONQUESTION) != IDYES) { rm_tree(dir); return 0; }
    wchar_t cur[MAX_PATH], bak[MAX_PATH], base[MAX_PATH]; GetModuleFileNameW(NULL, cur, MAX_PATH);
    _snwprintf(bak, MAX_PATH - 1, L"%s.old", cur); bak[MAX_PATH - 1] = 0; DeleteFileW(bak);
    if (!MoveFileExW(cur, bak, MOVEFILE_REPLACE_EXISTING)) { rm_tree(dir); MessageBoxW(owner, L"Impossible de remplacer l'application (dossier protégé en écriture ?).", L"Mise à jour", MB_ICONERROR); return 0; }
    if (!CopyFileW(newExe, cur, FALSE)) {
        MoveFileExW(bak, cur, MOVEFILE_REPLACE_EXISTING); rm_tree(dir);
        MessageBoxW(owner, L"Installation impossible : l'ancienne version a été restaurée.", L"Mise à jour", MB_ICONERROR); return 0; }
    /* nouveaux fichiers eventuels du zip (ex. listes iptv) : ajoutes seulement s'ils n'existent pas */
    { wchar_t *p = wcsrchr(newExe, L'\\'); if (p) { *p = 0; wchar_t src[MAX_PATH], dst[MAX_PATH]; _snwprintf(src, MAX_PATH - 1, L"%s\\iptv", newExe); src[MAX_PATH - 1] = 0;
        exe_dir(base); _snwprintf(dst, MAX_PATH - 1, L"%s\\iptv", base); dst[MAX_PATH - 1] = 0; copy_missing(src, dst); } }
    /* sources.txt : fusion des adresses (pour pouvoir actualiser les nouvelles playlists) */
    { wchar_t *p = wcsrchr(newExe, L'\\'); (void)p; wchar_t sp[MAX_PATH]; _snwprintf(sp, MAX_PATH - 1, L"%s\\iptv\\sources.txt", newExe); sp[MAX_PATH - 1] = 0;
      char *t = read_all(sp);
      if (t) { char *q = t; while (*q) {
          char *e = strchr(q, '\n'); size_t len = e ? (size_t)(e - q) : strlen(q);
          char line[1300]; if (len > 1299) len = 1299; memcpy(line, q, len); line[len] = 0;
          while (len && line[len - 1] == '\r') line[--len] = 0;
          q = e ? e + 1 : q + strlen(q);
          char *bar = strchr(line, '|'); if (!bar) continue; *bar = 0;
          wchar_t fw[300], uw[1100]; u8w(line, fw, 300); u8w(bar + 1, uw, 1100);
          wchar_t dp[MAX_PATH]; exe_dir(base); _snwprintf(dp, MAX_PATH - 1, L"%s\\iptv\\%s", base, fw); dp[MAX_PATH - 1] = 0;
          if (safe_file_name(fw) && !wcsncmp(uw, L"http", 4) && GetFileAttributesW(dp) != INVALID_FILE_ATTRIBUTES) sources_rewrite(NULL, fw, uw);
      } free(t); } }
    rm_tree(dir);
    ShellExecuteW(NULL, L"open", cur, NULL, NULL, SW_SHOWNORMAL);
    return 1;
}


/* ---------- mise a jour de l'application depuis GitHub (agentia-GIT/P-Lite) ---------- */
#define APP_VER_URL "https://raw.githubusercontent.com/agentia-GIT/P-Lite/main/version.txt"
#define APP_EXE_URL L"https://raw.githubusercontent.com/agentia-GIT/P-Lite/main/lecteur.exe"
static wchar_t gNewVer[32];
static int ver_cmp(const wchar_t *a, const wchar_t *b) {
    for (;;) {
        while (*a && !iswdigit(*a)) a++; while (*b && !iswdigit(*b)) b++;
        if (!*a && !*b) return 0;
        long x = 0, y = 0; while (iswdigit(*a)) x = x * 10 + (*a++ - L'0'); while (iswdigit(*b)) y = y * 10 + (*b++ - L'0');
        if (x != y) return x < y ? -1 : 1;
    }
}
static int app_remote_version(wchar_t *out) {                          /* version publiee dans le depot */
    char b[96]; out[0] = 0; if (!http_get_text(APP_VER_URL, b, sizeof b)) return 0;
    int n = 0; for (char *p = b; *p && n < 30; p++) { if ((*p >= '0' && *p <= '9') || *p == '.') out[n++] = (wchar_t)*p; else if (n) break; }
    out[n] = 0; return n > 0;
}
static int app_swap(HWND owner, const wchar_t *newExe) {              /* remplace lecteur.exe (l'ancien devient .old) */
    wchar_t cur[MAX_PATH], bak[MAX_PATH]; GetModuleFileNameW(NULL, cur, MAX_PATH);
    _snwprintf(bak, MAX_PATH - 1, L"%s.old", cur); bak[MAX_PATH - 1] = 0; DeleteFileW(bak);
    if (!MoveFileExW(cur, bak, MOVEFILE_REPLACE_EXISTING)) { MessageBoxW(owner, L"Impossible de remplacer l'application (dossier protégé en écriture ?).", L"Mise à jour", MB_ICONERROR); return 0; }
    if (!CopyFileW(newExe, cur, FALSE)) { MoveFileExW(bak, cur, MOVEFILE_REPLACE_EXISTING); MessageBoxW(owner, L"Installation impossible : l'ancienne version a été restaurée.", L"Mise à jour", MB_ICONERROR); return 0; }
    ShellExecuteW(NULL, L"open", cur, NULL, NULL, SW_SHOWNORMAL); return 1;
}
static int app_install_online(HWND owner) {                           /* telecharge lecteur.exe depuis GitHub puis l'installe */
    wchar_t tmp[MAX_PATH], f[MAX_PATH]; GetTempPathW(MAX_PATH, tmp); _snwprintf(f, MAX_PATH - 1, L"%slav_new_%lu.exe", tmp, GetTickCount()); f[MAX_PATH - 1] = 0;
    HCURSOR old = SetCursor(LoadCursor(NULL, IDC_WAIT)); ffAbort = 0; int ok = http_download(APP_EXE_URL, f, NULL, L"Lecteur A/V"); SetCursor(old);
    WIN32_FILE_ATTRIBUTE_DATA fa; unsigned char mz[2] = { 0, 0 }; DWORD rd = 0;
    if (ok) { HANDLE hf = CreateFileW(f, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL); if (hf != INVALID_HANDLE_VALUE) { ReadFile(hf, mz, 2, &rd, NULL); CloseHandle(hf); } }
    if (!ok || !GetFileAttributesExW(f, GetFileExInfoStandard, &fa) || fa.nFileSizeLow < 100000 || mz[0] != 'M' || mz[1] != 'Z') {
        DeleteFileW(f); MessageBoxW(owner, L"Téléchargement de la nouvelle version impossible.", L"Mise à jour", MB_ICONERROR); return 0; }
    int r = app_swap(owner, f); DeleteFileW(f); return r;
}
static void app_ini(wchar_t *p) { exe_dir(p); wcscat(p, L"\\capture.ini"); }
static DWORD WINAPI app_check_thread(LPVOID p) {                       /* verification au demarrage */
    (void)p; wchar_t v[32], ref[32] = L"", ip[MAX_PATH];
    if (app_remote_version(v) && ver_cmp(LAV_VERSION, v) < 0) {
        app_ini(ip); GetPrivateProfileStringW(L"capture", L"maj_refus", L"", ref, 32, ip);
        if (wcscmp(ref, v)) { wcscpy(gNewVer, v); PostMessage(hMain, WM_LAV_NEWVER, 0, 0); }
    }
    return 0;
}

static LRESULT CALLBACK SetProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CTLCOLORSTATIC: {
        int id = GetDlgCtrlID((HWND)lp);
        SetTextColor((HDC)wp, (id >= 410 && id < 420) || (id >= 450 && id < 460) ? C_FG : id == 420 ? statusClr : id == 421 ? ffStatusClr : C_DIM); SetBkMode((HDC)wp, TRANSPARENT); return (LRESULT)brDlg; }
    case WM_DRAWITEM: {
        DRAWITEMSTRUCT *d = (DRAWITEMSTRUCT *)lp;
        if (d->CtlID == 430 || d->CtlID == 432) {                      /* icone de mise a jour : fleche vers le bas sur une base */
            int dis = (d->itemState & ODS_DISABLED) != 0; RECT r = d->rcItem;
            fill(d->hDC, &r, dis ? C_BAR : ((d->itemState & ODS_SELECTED) ? C_TROU : C_HOT));
            COLORREF c = dis ? C_DIM : C_ACC; int cx = (r.left + r.right) / 2, cy = (r.top + r.bottom) / 2;
            frect(d->hDC, cx - S(2), cy - S(8), cx + S(2), cy + S(1), c);
            POINT t[3] = { { cx - S(7), cy }, { cx + S(7), cy }, { cx, cy + S(7) } }; poly(d->hDC, t, 3, c);
            frect(d->hDC, cx - S(8), cy + S(9), cx + S(8), cy + S(11), c);
        } else draw_btn(d, d->CtlID == 431);
        return TRUE; }
    case WM_SET_ONLINE: case WM_SET_UPD: set_refresh(); return 0;
    case WM_SET_FFONLINE: set_ff_refresh(); return 0;
    case WM_SET_FFUPD: if (ffUpdRunning) SetWindowTextW(hsFfStatus, ffMsg); else set_ff_refresh(); return 0;
    case WM_COMMAND:
        switch (LOWORD(wp)) {
        case 430: if (!updRunning) { updMsg[0] = 0; CloseHandle(CreateThread(NULL, 0, update_thread, h, 0, NULL)); Sleep(20); set_refresh(); } break;
        case 431: { wchar_t e[MAX_PATH]; GetModuleFileNameW(NULL, e, MAX_PATH); ShellExecuteW(NULL, L"open", e, NULL, NULL, SW_SHOWNORMAL); setDone = 1; PostMessage(hMain, WM_CLOSE, 0, 0); } break;
        case 434: { wchar_t v[32], t[160]; HCURSOR oc = SetCursor(LoadCursor(NULL, IDC_WAIT)); int ok = app_remote_version(v); SetCursor(oc);
            if (!ok) { SetWindowTextW(hsVal[0], LAV_VERSION); MessageBoxW(h, L"Impossible de joindre GitHub pour vérifier la version.", L"Mise à jour", MB_ICONINFORMATION); break; }
            if (ver_cmp(LAV_VERSION, v) < 0) {
                _snwprintf(t, 159, L"%s   —   version %s disponible", LAV_VERSION, v); t[159] = 0; SetWindowTextW(hsVal[0], t);
                _snwprintf(t, 159, L"La version %s est disponible (vous avez la %s).\n\nL'installer maintenant ?\nVos listes et votre configuration sont conservées.", v, LAV_VERSION); t[159] = 0;
                if (MessageBoxW(h, t, L"Mise à jour", MB_YESNO | MB_ICONQUESTION) == IDYES && app_install_online(h)) { setDone = 1; PostMessage(hMain, WM_CLOSE, 0, 0); }
            } else { _snwprintf(t, 159, L"%s   —   à jour", LAV_VERSION); t[159] = 0; SetWindowTextW(hsVal[0], t); }
        } break;
        case 433: if (!updRunning && !ffUpdRunning && !capRunning) { if (act_update_app(h)) { setDone = 1; PostMessage(hMain, WM_CLOSE, 0, 0); } } break;
        case 432: if (!ffUpdRunning && !capRunning) { ffMsg[0] = 0; CloseHandle(CreateThread(NULL, 0, ff_update_thread, h, 0, NULL)); Sleep(20); set_ff_refresh(); } break;
        case IDCANCEL: if (!updRunning && !ffUpdRunning) setDone = 1; break;
        }
        return 0;
    case WM_CLOSE: if (!updRunning && !ffUpdRunning) setDone = 1; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

static void settings_window(void) {
    static int reg = 0;
    if (!reg) {
        if (!brDlg) { brDlg = CreateSolidBrush(C_BAR); brEdit = CreateSolidBrush(C_BG); }
        WNDCLASSW wc; memset(&wc, 0, sizeof wc);
        wc.lpfnWndProc = SetProc; wc.hInstance = hInst; wc.lpszClassName = L"LavSet";
        wc.hbrBackground = brDlg; wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hIcon = LoadIconW(hInst, MAKEINTRESOURCEW(1));
        RegisterClassW(&wc); reg = 1;
    }
    setDone = 0; onlineState = 0; updMsg[0] = 0; updOk = 0;
    hSet = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LavSet", L"Paramètres", WS_POPUP | WS_CAPTION | WS_SYSMENU, 0, 0, 300, 200, hMain, NULL, hInst, NULL);
    int cw = S(640), ch = S(500);
    RECT wr, cr; GetWindowRect(hSet, &wr); GetClientRect(hSet, &cr);
    int ow = (wr.right - wr.left) - cr.right + cw, oh = (wr.bottom - wr.top) - cr.bottom + ch;
    RECT mr; GetWindowRect(hMain, &mr);
    SetWindowPos(hSet, NULL, mr.left + ((mr.right - mr.left) - ow) / 2, mr.top + ((mr.bottom - mr.top) - oh) / 2, ow, oh, SWP_NOZORDER);
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute");
               if (f) { f(hSet, 20, &dark, sizeof dark); f(hSet, 19, &dark, sizeof dark); } }
    const wchar_t *lab[5] = { L"Lecteur A/V", L"libmpv installée", L"FFmpeg intégré", L"Fichier DLL", L"Dernière version en ligne" };
    wchar_t val[5][300];
    wcscpy(val[0], LAV_VERSION); get_prop("mpv-version", val[1], 300); get_prop("ffmpeg-version", val[2], 300);
    { WIN32_FILE_ATTRIBUTE_DATA fa; wchar_t nm[MAX_PATH]; wcscpy(nm, wcsrchr(gDllPath, L'\\') ? wcsrchr(gDllPath, L'\\') + 1 : gDllPath);
      if (GetFileAttributesExW(gDllPath, GetFileExInfoStandard, &fa)) {
          FILETIME lf; SYSTEMTIME st; FileTimeToLocalFileTime(&fa.ftLastWriteTime, &lf); FileTimeToSystemTime(&lf, &st);
          _snwprintf(val[3], 299, L"%s   ·   %02d/%02d/%04d   ·   %.1f Mo", nm, st.wDay, st.wMonth, st.wYear, fa.nFileSizeLow / 1048576.0);
      } else wcscpy(val[3], nm); val[3][299] = 0; }
    wcscpy(val[4], L"Recherche en ligne…");
    for (int i = 0; i < 5; i++) {
        int y = S(22) + i * S(36); HWND c;
        c = CreateWindowExW(0, L"STATIC", lab[i], WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), y, S(190), S(22), hSet, (HMENU)(INT_PTR)(400 + i), hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
        hsVal[i] = CreateWindowExW(0, L"STATIC", val[i], WS_CHILD | WS_VISIBLE | SS_NOPREFIX | SS_ENDELLIPSIS, S(214), y, i == 4 ? S(360) : S(406), S(22), hSet, (HMENU)(INT_PTR)(410 + i), hInst, NULL);
        SendMessage(hsVal[i], WM_SETFONT, (WPARAM)fUI, 1);
    }
    hsUpd = CreateWindowExW(0, L"BUTTON", L"", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW | WS_DISABLED, S(588), S(22) + 4 * S(36) - S(4), S(32), S(30), hSet, (HMENU)430, hInst, NULL);
    hsStatus = CreateWindowExW(0, L"STATIC", L"", WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), S(22) + 5 * S(36) + S(8), S(600), S(40), hSet, (HMENU)420, hInst, NULL);
    SendMessage(hsStatus, WM_SETFONT, (WPARAM)fUI, 1);
    hsRestart = CreateWindowExW(0, L"BUTTON", L"Redémarrer", WS_CHILD | WS_TABSTOP | BS_OWNERDRAW, S(20), ch - S(12) - S(34), S(140), S(34), hSet, (HMENU)431, hInst, NULL);
    CreateWindowExW(0, L"BUTTON", L"Fermer", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, cw - S(12) - S(120), ch - S(12) - S(34), S(120), S(34), hSet, (HMENU)IDCANCEL, hInst, NULL);
    CreateWindowExW(0, L"BUTTON", L"Mettre \u00e0 jour depuis un zip\u2026", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, cw - S(12) - S(120) - S(12) - S(270), ch - S(12) - S(34), S(270), S(34), hSet, (HMENU)433, hInst, NULL);
    SetWindowPos(hsVal[0], NULL, 0, 0, S(210), S(22), SWP_NOMOVE | SWP_NOZORDER);
    CreateWindowExW(0, L"BUTTON", L"Vérifier les mises à jour", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, S(430), S(22) - S(4), S(190), S(30), hSet, (HMENU)434, hInst, NULL);
    statusClr = C_DIM;
    {   /* bibliotheque de capture : FFmpeg */
        const wchar_t *fl[3] = { L"Dossier codec", L"FFmpeg install\u00e9 (capture)", L"Derni\u00e8re version en ligne" };
        HWND hd = CreateWindowExW(0, L"STATIC", L"BIBLIOTH\u00c8QUE DE CAPTURE", WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), S(262), S(400), S(20), hSet, NULL, hInst, NULL); SendMessage(hd, WM_SETFONT, (WPARAM)fSmall, 1);
        wchar_t cd[MAX_PATH]; codec_dir(cd);
        for (int i = 0; i < 3; i++) {
            int y = S(290) + i * S(36); HWND c = CreateWindowExW(0, L"STATIC", fl[i], WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), y, S(190), S(22), hSet, (HMENU)(INT_PTR)(440 + i), hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
            hsFf[i] = CreateWindowExW(0, L"STATIC", L"", WS_CHILD | WS_VISIBLE | SS_NOPREFIX | SS_ENDELLIPSIS, S(214), y, i == 2 ? S(360) : S(406), S(22), hSet, (HMENU)(INT_PTR)(450 + i), hInst, NULL); SendMessage(hsFf[i], WM_SETFONT, (WPARAM)fUI, 1);
        }
        SetWindowTextW(hsFf[0], cd); SetWindowTextW(hsFf[1], L"Recherche\u2026"); SetWindowTextW(hsFf[2], L"Recherche en ligne\u2026");
        hsFfUpd = CreateWindowExW(0, L"BUTTON", L"", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW | WS_DISABLED, S(588), S(290) + 2 * S(36) - S(4), S(32), S(30), hSet, (HMENU)432, hInst, NULL);
        hsFfStatus = CreateWindowExW(0, L"STATIC", L"", WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), S(290) + 3 * S(36) + S(6), S(600), S(40), hSet, (HMENU)421, hInst, NULL); SendMessage(hsFfStatus, WM_SETFONT, (WPARAM)fUI, 1);
        ffStatusClr = C_DIM; ffOnlineState = 0; ffMsg[0] = 0; ffUpdOk = 0;
        CloseHandle(CreateThread(NULL, 0, ff_fetch_thread, hSet, 0, NULL));
    }
    CloseHandle(CreateThread(NULL, 0, fetch_thread, hSet, 0, NULL));

    int prevMenu = menuOpen; menuOpen = 1; EnableWindow(hMain, FALSE);
    ShowWindow(hSet, SW_SHOW); SetForegroundWindow(hSet);
    MSG msg;
    while (!setDone) {
        int r = GetMessage(&msg, NULL, 0, 0);
        if (r <= 0) { if (r == 0) PostQuitMessage((int)msg.wParam); break; }
        if (!IsDialogMessage(hSet, &msg)) { TranslateMessage(&msg); DispatchMessage(&msg); }
    }
    EnableWindow(hMain, TRUE); DestroyWindow(hSet); hSet = NULL; menuOpen = prevMenu;
    SetForegroundWindow(hMain);
}


/* ================= installation des bibliotheques manquantes (dossier codec) ================= */
#define WM_INST_DONE (WM_APP + 21)
static int instState, instNeedMpv, instNeedFf; static wchar_t instErr[300];
static void make_fonts(void);
static LRESULT CALLBACK InstProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_CTLCOLORSTATIC: SetTextColor((HDC)wp, GetDlgCtrlID((HWND)lp) == 420 ? C_FG : C_DIM); SetBkMode((HDC)wp, TRANSPARENT); return (LRESULT)brDlg;
    case WM_DRAWITEM: draw_btn((DRAWITEMSTRUCT *)lp, 0); return TRUE;
    case WM_SET_UPD: if (updRunning) SetWindowTextW(GetDlgItem(h, 420), updMsg); return 0;
    case WM_SET_FFUPD: SetWindowTextW(GetDlgItem(h, 420), ffMsg); return 0;
    case WM_INST_DONE: if (instState == 0) instState = wp ? 1 : 2; return 0;
    case WM_COMMAND: if (LOWORD(wp) == IDCANCEL) { instState = 3; ffAbort = 1; } return 0;
    case WM_CLOSE: instState = 3; ffAbort = 1; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}
static DWORD WINAPI install_thread(LPVOID a) {
    HWND h = (HWND)a; int ok = 1; instErr[0] = 0;
    if (instNeedMpv) {
        fetch_thread(h);
        if (onlineState == 1) { updMsg[0] = 0; update_thread(h); ok = updOk; if (!ok) wcsncpy(instErr, updMsg, 299); }
        else { ok = 0; wcscpy(instErr, L"Serveur de téléchargement injoignable (hors ligne ?)."); }
    }
    if (ok && instNeedFf) {
        ff_fetch_thread(h); ffUpdRunning = 1; ffAbort = 0; ffUpdOk = ff_install(h); ffUpdRunning = 0; ok = ffUpdOk;
        if (!ok) wcsncpy(instErr, ffMsg, 299);
    }
    instErr[299] = 0;
    if (IsWindow(h)) PostMessage(h, WM_INST_DONE, ok, 0);
    return 0;
}

/* renvoie 1 = installe, 0 = echec / annule, -1 = refuse a la question */
static int install_window(int needMpv, int needFf, int ask) {
    if (ask) {
        wchar_t q[600] = L"Bibliothèques manquantes dans le dossier « codec » :\n\n";
        if (needMpv) wcscat(q, L"   •  libmpv (lecture audio / vidéo)  —  environ 30 Mo\n");
        if (needFf) wcscat(q, L"   •  FFmpeg (capture d'écran)  —  environ 90 Mo\n");
        wcscat(q, L"\nLes télécharger et les installer maintenant ?");
        if (MessageBoxW(hMain, q, L"Lecteur A/V", MB_YESNO | MB_ICONQUESTION) != IDYES) return -1;
    }
    if (!fUI) make_fonts();
    if (!brDlg) { brDlg = CreateSolidBrush(C_BAR); brEdit = CreateSolidBrush(C_BG); }
    { wchar_t d[MAX_PATH]; codec_dir(d); CreateDirectoryW(d, NULL); if (needMpv) { _snwprintf(gDllPath, MAX_PATH - 1, L"%s\\libmpv-2.dll", d); gDllPath[MAX_PATH - 1] = 0; } }
    static int reg = 0;
    if (!reg) {
        WNDCLASSW wc; memset(&wc, 0, sizeof wc);
        wc.lpfnWndProc = InstProc; wc.hInstance = hInst; wc.lpszClassName = L"LavInst";
        wc.hbrBackground = brDlg; wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hIcon = LoadIconW(hInst, MAKEINTRESOURCEW(1));
        RegisterClassW(&wc); reg = 1;
    }
    HWND h = CreateWindowExW(WS_EX_DLGMODALFRAME, L"LavInst", L"Installation des bibliothèques", WS_POPUP | WS_CAPTION | WS_SYSMENU, 0, 0, 300, 200, hMain, NULL, hInst, NULL);
    int cw = S(520), ch = S(150);
    RECT wr, cr; GetWindowRect(h, &wr); GetClientRect(h, &cr);
    int ow = (wr.right - wr.left) - cr.right + cw, oh = (wr.bottom - wr.top) - cr.bottom + ch;
    SetWindowPos(h, NULL, (GetSystemMetrics(SM_CXSCREEN) - ow) / 2, (GetSystemMetrics(SM_CYSCREEN) - oh) / 2, ow, oh, SWP_NOZORDER);
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute");
               if (f) { f(h, 20, &dark, sizeof dark); f(h, 19, &dark, sizeof dark); } }
    HWND c = CreateWindowExW(0, L"STATIC", L"Installation des bibliothèques…", WS_CHILD | WS_VISIBLE, S(20), S(20), S(480), S(20), h, NULL, hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
    c = CreateWindowExW(0, L"STATIC", L"Recherche de la dernière version…", WS_CHILD | WS_VISIBLE | SS_NOPREFIX, S(20), S(52), S(480), S(44), h, (HMENU)420, hInst, NULL); SendMessage(c, WM_SETFONT, (WPARAM)fUI, 1);
    CreateWindowExW(0, L"BUTTON", L"Annuler", WS_CHILD | WS_VISIBLE | WS_TABSTOP | BS_OWNERDRAW, cw - S(12) - S(110), ch - S(12) - S(32), S(110), S(32), h, (HMENU)IDCANCEL, hInst, NULL);
    instState = 0; instNeedMpv = needMpv; instNeedFf = needFf; onlineState = 0; updMsg[0] = 0; updOk = 0; ffAbort = 0;
    int prevMenu = menuOpen; menuOpen = 1; if (IsWindow(hMain) && IsWindowVisible(hMain)) EnableWindow(hMain, FALSE);
    ShowWindow(h, SW_SHOW); SetForegroundWindow(h);
    CloseHandle(CreateThread(NULL, 0, install_thread, h, 0, NULL));
    MSG msg;
    while (instState == 0) {
        int r = GetMessage(&msg, NULL, 0, 0);
        if (r <= 0) { instState = 3; break; }
        if (!IsDialogMessage(h, &msg)) { TranslateMessage(&msg); DispatchMessage(&msg); }
    }
    if (IsWindow(hMain)) EnableWindow(hMain, TRUE);
    DestroyWindow(h); menuOpen = prevMenu;
    if (instState == 1) {
        if (needMpv) { wchar_t e[MAX_PATH]; GetModuleFileNameW(NULL, e, MAX_PATH); ShellExecuteW(NULL, L"open", e, NULL, NULL, SW_SHOWNORMAL); }
        return 1;
    }
    if (instState == 2) {
        wchar_t t[700]; const wchar_t *hint = needMpv
            ? L"Installation manuelle : placez libmpv-2.dll (x64) dans le dossier codec, à côté de lecteur.exe.\nhttps://github.com/shinchiro/mpv-winbuild-cmake/releases"
            : L"Installation manuelle : placez ffmpeg.exe (x64) dans le dossier codec, à côté de lecteur.exe.\nhttps://www.gyan.dev/ffmpeg/builds/";
        _snwprintf(t, 699, L"%s\n\n%s", instErr, hint); t[699] = 0;
        MessageBoxW(IsWindow(hMain) ? hMain : NULL, t, L"Lecteur A/V", MB_ICONERROR);
    }
    return 0;
}


/* ================= capture video + audio du PC (FFmpeg + WASAPI loopback) ================= */
#define WM_CAP_DONE (WM_APP + 20)
#ifndef WDA_EXCLUDEFROMCAPTURE
#define WDA_EXCLUDEFROMCAPTURE 0x11
#endif
enum { CM_SCREEN, CM_ZONE, CM_WINDOW };
typedef struct { int mode, crf, fps, abr, speed, audio, cursor, fmt, syncMs, hasZone; RECT zone; wchar_t outdir[MAX_PATH]; } CapCfg;
static CapCfg cc = { CM_SCREEN, 26, 30, 160, 1, 1, 1, 0, 0, 0, { 0, 0, 0, 0 }, L"" };
static HWND hCap, capWin, hZone;
static int capMon = -1, capHover = -1, capDrag = -1, capStopping, capCloseAfter, zoneState, zoneDrag;
static DWORD capT0;
static wchar_t capLast[MAX_PATH], capCurOut[MAX_PATH], capStatus[420], capPipeName[80];
static COLORREF capStatusClr;
static HANDLE capProc, capIn, capErrR, capErrThr, capStopThr, aThread, aPipe, aEvInit, aEvGo, evStop;
static char capErr[2048]; static CRITICAL_SECTION csErr; static int csInit;
static struct { RECT r; wchar_t name[96]; int primary; } mons[16]; static int nMons;
static struct { HWND h; wchar_t t[80]; } wl[48]; static int nWl;
static RECT zoneSel; static POINT zoneA;
static struct { int rate, ch, bpf; wchar_t fmt[8]; } aInfo; static volatile int aInitOk;

/* ----- configuration (capture.ini a cote de l'exe) ----- */
static void cap_ini_path(wchar_t *p) { exe_dir(p); wcscat(p, L"\\capture.ini"); }
static int ini_i(const wchar_t *k, int d) {
    wchar_t p[MAX_PATH], b[32]; cap_ini_path(p);
    GetPrivateProfileStringW(L"capture", k, L"", b, 32, p); return b[0] ? _wtoi(b) : d;
}
static void ini_si(const wchar_t *k, int v) { wchar_t p[MAX_PATH], b[32]; cap_ini_path(p); _snwprintf(b, 31, L"%d", v); WritePrivateProfileStringW(L"capture", k, b, p); }
static int clampi(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }
static int dir_exists(const wchar_t *d) { DWORD a = GetFileAttributesW(d); return a != INVALID_FILE_ATTRIBUTES && (a & FILE_ATTRIBUTE_DIRECTORY); }
static void desktop_dir(wchar_t *o) { if (FAILED(SHGetFolderPathW(NULL, CSIDL_DESKTOPDIRECTORY, NULL, SHGFP_TYPE_CURRENT, o))) o[0] = 0; }

static void cap_load(void) {
    wchar_t p[MAX_PATH]; cap_ini_path(p);
    cc.mode = clampi(ini_i(L"mode", 0), 0, 2);
    cc.crf = clampi(ini_i(L"crf", 26), 18, 34);
    cc.fps = clampi((ini_i(L"fps", 30) + 2) / 5 * 5, 10, 60);
    cc.abr = clampi(ini_i(L"audio_kbps", 160) / 16 * 16, 64, 320);
    cc.speed = clampi(ini_i(L"vitesse", 1), 0, 3);
    cc.audio = ini_i(L"son_pc", 1) != 0; cc.cursor = ini_i(L"curseur", 1) != 0; cc.fmt = ini_i(L"format", 0) ? 1 : 0;
    cc.syncMs = clampi(ini_i(L"decalage_audio_ms", 0), -1000, 1000);
    cc.hasZone = ini_i(L"zone_ok", 0);
    cc.zone.left = ini_i(L"zone_g", 0); cc.zone.top = ini_i(L"zone_h", 0); cc.zone.right = ini_i(L"zone_d", 0); cc.zone.bottom = ini_i(L"zone_b", 0);
    if (cc.zone.right - cc.zone.left < 16 || cc.zone.bottom - cc.zone.top < 16) cc.hasZone = 0;
    GetPrivateProfileStringW(L"capture", L"dossier", L"", cc.outdir, MAX_PATH, p);
    if (!cc.outdir[0] || !dir_exists(cc.outdir)) desktop_dir(cc.outdir);      /* defaut : bureau de l'utilisateur */
}
static void cap_save(void) {
    wchar_t p[MAX_PATH]; cap_ini_path(p);
    ini_si(L"mode", cc.mode); ini_si(L"crf", cc.crf); ini_si(L"fps", cc.fps); ini_si(L"audio_kbps", cc.abr); ini_si(L"vitesse", cc.speed);
    ini_si(L"son_pc", cc.audio); ini_si(L"curseur", cc.cursor); ini_si(L"format", cc.fmt); ini_si(L"decalage_audio_ms", cc.syncMs);
    ini_si(L"zone_ok", cc.hasZone); ini_si(L"zone_g", cc.zone.left); ini_si(L"zone_h", cc.zone.top); ini_si(L"zone_d", cc.zone.right); ini_si(L"zone_b", cc.zone.bottom);
    WritePrivateProfileStringW(L"capture", L"dossier", cc.outdir, p);
}

/* ----- ecrans, fenetres ----- */
static BOOL CALLBACK mon_cb(HMONITOR hm, HDC dc, LPRECT r, LPARAM lp) {
    (void)dc; (void)r; (void)lp; if (nMons >= 16) return FALSE;
    MONITORINFO mi; memset(&mi, 0, sizeof mi); mi.cbSize = sizeof mi; if (!GetMonitorInfoW(hm, &mi)) return TRUE;
    mons[nMons].r = mi.rcMonitor; mons[nMons].primary = (mi.dwFlags & MONITORINFOF_PRIMARY) != 0;
    _snwprintf(mons[nMons].name, 95, L"Écran %d — %d×%d%s", nMons + 1, (int)(mi.rcMonitor.right - mi.rcMonitor.left), (int)(mi.rcMonitor.bottom - mi.rcMonitor.top),
               mons[nMons].primary ? L"  (principal)" : L"");
    nMons++; return TRUE;
}
static void mons_refresh(void) {
    nMons = 0; EnumDisplayMonitors(NULL, NULL, mon_cb, 0);
    if (capMon < 0 || capMon > nMons) { capMon = 1; for (int i = 0; i < nMons; i++) if (mons[i].primary) capMon = i + 1; if (!nMons) capMon = 0; }
}
static HRESULT dwm_attr(HWND h, DWORD a, void *v, DWORD sz) {
    static HRESULT (WINAPI *f)(HWND, DWORD, PVOID, DWORD); static int init;
    if (!init) { HMODULE d = LoadLibraryW(L"dwmapi.dll"); if (d) f = (void *)GetProcAddress(d, "DwmGetWindowAttribute"); init = 1; }
    return f ? f(h, a, v, sz) : E_FAIL;
}
static void win_rect(HWND h, RECT *r) { if (FAILED(dwm_attr(h, 9, r, sizeof *r))) GetWindowRect(h, r); }
static BOOL CALLBACK win_cb(HWND h, LPARAM lp) {
    (void)lp; if (nWl >= 48 || h == hCap || !IsWindowVisible(h) || IsIconic(h)) return TRUE;
    LONG ex = GetWindowLong(h, GWL_EXSTYLE);
    if ((ex & WS_EX_TOOLWINDOW) && !(ex & WS_EX_APPWINDOW)) return TRUE;
    if (GetWindow(h, GW_OWNER) && !(ex & WS_EX_APPWINDOW)) return TRUE;
    wchar_t t[160]; if (GetWindowTextW(h, t, 160) <= 0) return TRUE;
    DWORD cl = 0; dwm_attr(h, 14, &cl, sizeof cl); if (cl) return TRUE;
    RECT r; GetWindowRect(h, &r); if (r.right - r.left < 64 || r.bottom - r.top < 64) return TRUE;
    wl[nWl].h = h; wcsncpy(wl[nWl].t, t, 79); wl[nWl].t[79] = 0; nWl++; return TRUE;
}

static int cap_region(RECT *o, wchar_t *err) {
    RECT v, r; v.left = GetSystemMetrics(SM_XVIRTUALSCREEN); v.top = GetSystemMetrics(SM_YVIRTUALSCREEN);
    v.right = v.left + GetSystemMetrics(SM_CXVIRTUALSCREEN); v.bottom = v.top + GetSystemMetrics(SM_CYVIRTUALSCREEN);
    if (cc.mode == CM_SCREEN) { mons_refresh(); r = (capMon > 0 && capMon <= nMons) ? mons[capMon - 1].r : v; }
    else if (cc.mode == CM_ZONE) { if (!cc.hasZone) { wcscpy(err, L"Aucune zone sélectionnée."); return 0; } r = cc.zone; }
    else { if (!capWin || !IsWindow(capWin) || IsIconic(capWin)) { wcscpy(err, L"Choisissez d'abord une fenêtre (non réduite)."); return 0; } win_rect(capWin, &r); }
    if (!IntersectRect(o, &r, &v)) { wcscpy(err, L"La zone est en dehors de l'écran."); return 0; }
    o->right = o->left + ((o->right - o->left) & ~1); o->bottom = o->top + ((o->bottom - o->top) & ~1);
    if (o->right - o->left < 16 || o->bottom - o->top < 16) { wcscpy(err, L"Zone trop petite."); return 0; }
    return 1;
}

/* ----- selection d'une zone libre a la souris ----- */
static LRESULT CALLBACK ZoneProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_ERASEBKGND: return 1;
    case WM_SETCURSOR: SetCursor(LoadCursor(NULL, IDC_CROSS)); return TRUE;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT rc; GetClientRect(h, &rc);
        HDC md = CreateCompatibleDC(dc); HBITMAP bm = CreateCompatibleBitmap(dc, rc.right, rc.bottom); HGDIOBJ old = SelectObject(md, bm);
        fill(md, &rc, RGB(8, 10, 14));
        if (zoneSel.right > zoneSel.left && zoneSel.bottom > zoneSel.top) {
            RECT s = zoneSel; fill(md, &s, RGB(255, 0, 255));
            frect(md, s.left - 2, s.top - 2, s.right + 2, s.top, C_ACC); frect(md, s.left - 2, s.bottom, s.right + 2, s.bottom + 2, C_ACC);
            frect(md, s.left - 2, s.top, s.left, s.bottom, C_ACC); frect(md, s.right, s.top, s.right + 2, s.bottom, C_ACC);
            wchar_t t[60]; _snwprintf(t, 59, L"%d × %d", (int)(s.right - s.left), (int)(s.bottom - s.top)); t[59] = 0;
            RECT tr = { s.left, s.top - S(26), s.left + S(110), s.top - S(4) }; if (tr.top < 0) { tr.top = s.top + S(4); tr.bottom = tr.top + S(22); }
            fill(md, &tr, C_BAR); text(md, t, &tr, C_ACC, fUI, DT_CENTER);
        } else {
            RECT tr = rc; text(md, L"Faites glisser pour choisir la zone à capturer   ·   Échap pour annuler", &tr, RGB(235, 238, 242), fUI, DT_CENTER);
        }
        BitBlt(dc, 0, 0, rc.right, rc.bottom, md, 0, 0, SRCCOPY);
        SelectObject(md, old); DeleteObject(bm); DeleteDC(md); EndPaint(h, &ps); return 0; }
    case WM_LBUTTONDOWN: zoneA.x = GET_X_LPARAM(lp); zoneA.y = GET_Y_LPARAM(lp); zoneDrag = 1; SetCapture(h); SetRectEmpty(&zoneSel); return 0;
    case WM_MOUSEMOVE:
        if (zoneDrag) {
            int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
            zoneSel.left = min(zoneA.x, x); zoneSel.right = max(zoneA.x, x); zoneSel.top = min(zoneA.y, y); zoneSel.bottom = max(zoneA.y, y);
            InvalidateRect(h, NULL, FALSE);
        }
        return 0;
    case WM_LBUTTONUP:
        if (zoneDrag) { zoneDrag = 0; ReleaseCapture(); zoneState = (zoneSel.right - zoneSel.left >= 32 && zoneSel.bottom - zoneSel.top >= 32) ? 1 : 2; }
        return 0;
    case WM_RBUTTONDOWN: zoneState = 2; return 0;
    case WM_KEYDOWN: if (wp == VK_ESCAPE) zoneState = 2; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}
static void cap_pick_zone(void) {
    static int reg = 0;
    if (!reg) { WNDCLASSW wc; memset(&wc, 0, sizeof wc); wc.lpfnWndProc = ZoneProc; wc.hInstance = hInst; wc.lpszClassName = L"LavZone"; wc.hCursor = LoadCursor(NULL, IDC_CROSS); RegisterClassW(&wc); reg = 1; }
    int vx = GetSystemMetrics(SM_XVIRTUALSCREEN), vy = GetSystemMetrics(SM_YVIRTUALSCREEN), vw = GetSystemMetrics(SM_CXVIRTUALSCREEN), vh = GetSystemMetrics(SM_CYVIRTUALSCREEN);
    zoneState = 0; zoneDrag = 0; SetRectEmpty(&zoneSel);
    ShowWindow(hCap, SW_HIDE);
    hZone = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW, L"LavZone", L"", WS_POPUP, vx, vy, vw, vh, NULL, NULL, hInst, NULL);
    SetLayeredWindowAttributes(hZone, RGB(255, 0, 255), 130, LWA_COLORKEY | LWA_ALPHA);
    ShowWindow(hZone, SW_SHOW); SetForegroundWindow(hZone); SetFocus(hZone);
    MSG msg;
    while (!zoneState) {
        int r = GetMessage(&msg, NULL, 0, 0);
        if (r <= 0) { if (r == 0) PostQuitMessage((int)msg.wParam); break; }
        TranslateMessage(&msg); DispatchMessage(&msg);
    }
    DestroyWindow(hZone); hZone = NULL;
    if (zoneState == 1) {
        cc.zone.left = zoneSel.left + vx; cc.zone.right = zoneSel.right + vx; cc.zone.top = zoneSel.top + vy; cc.zone.bottom = zoneSel.bottom + vy;
        cc.hasZone = 1; cc.mode = CM_ZONE; cap_save();
    }
    ShowWindow(hCap, SW_SHOW); SetForegroundWindow(hCap); InvalidateRect(hCap, NULL, FALSE);
}

/* ----- audio du PC : WASAPI loopback -> tube nomme -> FFmpeg ----- */
static const GUID G_CLSID_MMDevEnum = { 0xBCDE0395, 0xE52F, 0x467C, { 0x8E, 0x3D, 0xC4, 0x57, 0x92, 0x91, 0x69, 0x2E } };
static const GUID G_IID_IMMDevEnum  = { 0xA95664D2, 0x9614, 0x4F35, { 0xA7, 0x46, 0xDE, 0x8D, 0xB6, 0x36, 0x17, 0xE6 } };
static const GUID G_IID_IAudioClient = { 0x1CB9AD4C, 0xDBFA, 0x4C32, { 0xB1, 0x78, 0xC2, 0xF5, 0x68, 0xA7, 0x03, 0xB2 } };
static const GUID G_IID_IACapture   = { 0xC8ADBD64, 0xE71E, 0x48A0, { 0xA4, 0xDE, 0x18, 0x5C, 0x39, 0x5C, 0xD3, 0x17 } };
static const GUID G_SUB_FLOAT = { 0x00000003, 0x0000, 0x0010, { 0x80, 0x00, 0x00, 0xAA, 0x00, 0x38, 0x9B, 0x71 } };
static const GUID G_SUB_PCM   = { 0x00000001, 0x0000, 0x0010, { 0x80, 0x00, 0x00, 0xAA, 0x00, 0x38, 0x9B, 0x71 } };

static int write_all(HANDLE h, const BYTE *b, DWORD n) { while (n) { DWORD w = 0; if (!WriteFile(h, b, n, &w, NULL) || !w) return 0; b += w; n -= w; } return 1; }
static int write_silence(HANDLE h, const BYTE *zero, int rate, int bpf, long long frames) {
    while (frames > 0) { long long c = frames > rate ? rate : frames; if (!write_all(h, zero, (DWORD)(c * bpf))) return 0; frames -= c; }
    return 1;
}
static long long now100(void) { static LARGE_INTEGER f; LARGE_INTEGER c; if (!f.QuadPart) QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c); return (long long)((double)c.QuadPart * 1e7 / (double)f.QuadPart); }

static DWORD WINAPI audio_thread(LPVOID a) {
    (void)a;
    IMMDeviceEnumerator *en = NULL; IMMDevice *dev = NULL; IAudioClient *ac = NULL; IAudioCaptureClient *cl = NULL; WAVEFORMATEX *wf = NULL;
    BYTE *zero = NULL; int ok = 0, started = 0; HRESULT hr;
    CoInitializeEx(NULL, COINIT_MULTITHREADED);
    hr = CoCreateInstance(&G_CLSID_MMDevEnum, NULL, CLSCTX_ALL, &G_IID_IMMDevEnum, (void **)&en);
    if (SUCCEEDED(hr)) hr = IMMDeviceEnumerator_GetDefaultAudioEndpoint(en, eRender, eConsole, &dev);
    if (SUCCEEDED(hr)) hr = IMMDevice_Activate(dev, &G_IID_IAudioClient, CLSCTX_ALL, NULL, (void **)&ac);
    if (SUCCEEDED(hr)) hr = IAudioClient_GetMixFormat(ac, &wf);
    if (SUCCEEDED(hr)) {
        int isF = wf->wFormatTag == WAVE_FORMAT_IEEE_FLOAT, isP = wf->wFormatTag == WAVE_FORMAT_PCM;
        if (wf->wFormatTag == WAVE_FORMAT_EXTENSIBLE) { WAVEFORMATEXTENSIBLE *we = (WAVEFORMATEXTENSIBLE *)wf; isF = IsEqualGUID(&we->SubFormat, &G_SUB_FLOAT); isP = IsEqualGUID(&we->SubFormat, &G_SUB_PCM); }
        const wchar_t *fn = NULL;
        if (isF && wf->wBitsPerSample == 32) fn = L"f32le"; else if (isP && wf->wBitsPerSample == 16) fn = L"s16le";
        else if (isP && wf->wBitsPerSample == 24) fn = L"s24le"; else if (isP && wf->wBitsPerSample == 32) fn = L"s32le";
        if (fn) { wcscpy(aInfo.fmt, fn); aInfo.rate = (int)wf->nSamplesPerSec; aInfo.ch = wf->nChannels; aInfo.bpf = wf->nBlockAlign;
                  hr = IAudioClient_Initialize(ac, AUDCLNT_SHAREMODE_SHARED, AUDCLNT_STREAMFLAGS_LOOPBACK, 10000000, 0, wf, NULL); }
        else hr = E_FAIL;
    }
    if (SUCCEEDED(hr)) hr = IAudioClient_GetService(ac, &G_IID_IACapture, (void **)&cl);
    ok = SUCCEEDED(hr); aInitOk = ok; SetEvent(aEvInit);
    if (!ok) goto out;
    { HANDLE w2[2] = { aEvGo, evStop }; if (WaitForMultipleObjects(2, w2, FALSE, 20000) != WAIT_OBJECT_0) goto out; }
    if (!ConnectNamedPipe(aPipe, NULL) && GetLastError() != ERROR_PIPE_CONNECTED) goto out;
    if (WaitForSingleObject(evStop, 0) == WAIT_OBJECT_0) goto out;
    {
        const int rate = aInfo.rate, bpf = aInfo.bpf; const long long thr = (long long)rate * 3 / 100;
        long long t0 = now100() + (long long)cc.syncMs * 10000, sent = 0; int alive = 1;
        zero = (BYTE *)calloc((size_t)rate, (size_t)bpf); if (!zero) goto out;
        IAudioClient_Start(ac); started = 1;
        while (alive && WaitForSingleObject(evStop, 0) != WAIT_OBJECT_0) {
            UINT32 np = 0; int got = 0;
            while (alive && SUCCEEDED(IAudioCaptureClient_GetNextPacketSize(cl, &np)) && np) {
                BYTE *d = NULL; UINT32 n = 0; DWORD fl = 0; UINT64 qp = 0;
                if (FAILED(IAudioCaptureClient_GetBuffer(cl, &d, &n, &fl, NULL, &qp))) break;
                UINT32 nf = n;
                long long ex = qp ? ((long long)qp - t0) * rate / 10000000LL : sent; BYTE *p = d;
                if (ex < 0) { UINT32 sk = (UINT32)(-ex < (long long)n ? -ex : n); p += (size_t)sk * bpf; n -= sk; ex += sk; }
                if (n) {
                    if (ex > sent + thr) { if (!write_silence(aPipe, zero, rate, bpf, ex - sent)) alive = 0; else sent = ex; }
                    else if (sent > ex + thr) { UINT32 dr = (UINT32)(sent - ex < (long long)n ? sent - ex : n); p += (size_t)dr * bpf; n -= dr; }
                    if (alive && n) {
                        int w = (fl & AUDCLNT_BUFFERFLAGS_SILENT) ? write_silence(aPipe, zero, rate, bpf, n) : write_all(aPipe, p, (DWORD)n * bpf);
                        if (!w) alive = 0; else sent += n;
                    }
                }
                IAudioCaptureClient_ReleaseBuffer(cl, nf);
                got = 1;
            }
            if (!got && alive) {                      /* rien a lire (silence du PC) : on garde la ligne de temps continue */
                long long cur = (now100() - t0) * rate / 10000000LL;
                if (cur > sent + rate / 20) { if (!write_silence(aPipe, zero, rate, bpf, cur - sent)) alive = 0; else sent = cur; }
            }
            Sleep(8);
        }
    }
out:
    if (started) IAudioClient_Stop(ac);
    if (cl) IAudioCaptureClient_Release(cl);
    if (ac) IAudioClient_Release(ac);
    if (dev) IMMDevice_Release(dev);
    if (en) IMMDeviceEnumerator_Release(en);
    if (wf) CoTaskMemFree(wf);
    free(zero);
    if (aPipe) { CloseHandle(aPipe); aPipe = NULL; }
    CoUninitialize();
    return 0;
}

static void audio_stop(void) {
    if (!aThread) return;
    SetEvent(evStop);
    if (WaitForSingleObject(aThread, 600) == WAIT_TIMEOUT) {          /* peut-etre bloque dans ConnectNamedPipe */
        if (capPipeName[0]) { HANDLE c = CreateFileW(capPipeName, GENERIC_READ, 0, NULL, OPEN_EXISTING, 0, NULL); if (c != INVALID_HANDLE_VALUE) CloseHandle(c); }
        WaitForSingleObject(aThread, 2500);
    }
    CloseHandle(aThread); aThread = NULL;
}

/* ffmpeg.exe doit etre "DPI aware" pour que gdigrab capture les vrais pixels (affichage a 125 %, 150 %...) */
static void ff_dpi_shim(const wchar_t *exe) {
    HKEY k;
    if (RegCreateKeyExW(HKEY_CURRENT_USER, L"Software\\Microsoft\\Windows NT\\CurrentVersion\\AppCompatFlags\\Layers", 0, NULL, 0, KEY_QUERY_VALUE | KEY_SET_VALUE, NULL, &k, NULL) != ERROR_SUCCESS) return;
    wchar_t cur[300] = L"", nv[340]; DWORD sz = sizeof cur - 2, ty = 0;
    if (RegQueryValueExW(k, exe, NULL, &ty, (BYTE *)cur, &sz) != ERROR_SUCCESS) cur[0] = 0;
    if (!wcsstr(cur, L"HIGHDPIAWARE")) {
        if (cur[0] == L'~') _snwprintf(nv, 339, L"%s HIGHDPIAWARE", cur); else wcscpy(nv, L"~ HIGHDPIAWARE");
        nv[339] = 0; RegSetValueExW(k, exe, 0, REG_SZ, (const BYTE *)nv, (DWORD)((wcslen(nv) + 1) * sizeof(wchar_t)));
    }
    RegCloseKey(k);
}

static void cap_set_status(const wchar_t *m, COLORREF c) { wcsncpy(capStatus, m, 419); capStatus[419] = 0; capStatusClr = c; if (hCap) InvalidateRect(hCap, NULL, FALSE); }

static DWORD WINAPI cap_err_thread(LPVOID a) {
    (void)a; char b[512]; DWORD n;
    while (ReadFile(capErrR, b, sizeof b, &n, NULL) && n) {
        EnterCriticalSection(&csErr);
        size_t l = strlen(capErr);
        if (l + n >= sizeof capErr) { size_t drop = l + n - (sizeof capErr - 1); if (drop > l) drop = l; memmove(capErr, capErr + drop, l - drop + 1); l -= drop; }
        if (n < sizeof capErr - 1 - l) { memcpy(capErr + l, b, n); capErr[l + n] = 0; }
        LeaveCriticalSection(&csErr);
    }
    return 0;
}

static void cap_free_events(void) {
    if (aEvInit) { CloseHandle(aEvInit); aEvInit = NULL; } if (aEvGo) { CloseHandle(aEvGo); aEvGo = NULL; } if (evStop) { CloseHandle(evStop); evStop = NULL; }
}

static void cap_start(void) {
    wchar_t err[200] = L"", ffp[MAX_PATH], cl[4000], ain[420] = L"", aout[120] = L"-an ";
    RECT rg; int useAudio = cc.audio;
    if (!csInit) { InitializeCriticalSection(&csErr); csInit = 1; }
    if (!ff_present()) { cap_set_status(L"FFmpeg introuvable dans le dossier codec (Paramètres > FFmpeg).", C_RED); return; }
    if (!cap_region(&rg, err)) { cap_set_status(err, C_RED); return; }
    if (!dir_exists(cc.outdir) && !CreateDirectoryW(cc.outdir, NULL)) desktop_dir(cc.outdir);
    SYSTEMTIME st; GetLocalTime(&st);
    _snwprintf(capCurOut, MAX_PATH - 1, L"%s\\Capture_%04d-%02d-%02d_%02d-%02d-%02d.%s", cc.outdir, st.wYear, st.wMonth, st.wDay, st.wHour, st.wMinute, st.wSecond, cc.fmt ? L"mp4" : L"mkv");
    capCurOut[MAX_PATH - 1] = 0;
    aEvInit = CreateEventW(NULL, TRUE, FALSE, NULL); aEvGo = CreateEventW(NULL, TRUE, FALSE, NULL); evStop = CreateEventW(NULL, TRUE, FALSE, NULL);
    capPipeName[0] = 0; aInitOk = 0;
    if (useAudio) {
        _snwprintf(capPipeName, 79, L"\\\\.\\pipe\\lav_audio_%lu_%lu", GetCurrentProcessId(), GetTickCount());
        aPipe = CreateNamedPipeW(capPipeName, PIPE_ACCESS_OUTBOUND, PIPE_TYPE_BYTE | PIPE_WAIT, 1, 1 << 22, 0, 0, NULL);
        if (aPipe == INVALID_HANDLE_VALUE) { aPipe = NULL; useAudio = 0; }
        else {
            aThread = CreateThread(NULL, 0, audio_thread, NULL, 0, NULL);
            WaitForSingleObject(aEvInit, 6000);
            if (!aInitOk) {
                SetEvent(evStop); WaitForSingleObject(aThread, 3000); CloseHandle(aThread); aThread = NULL;
                if (MessageBoxW(hCap, L"Le flux audio du PC est indisponible.\n\nEnregistrer la vidéo sans le son ?", L"Capture", MB_YESNO | MB_ICONQUESTION) != IDYES) { cap_free_events(); return; }
                useAudio = 0; capPipeName[0] = 0;
            }
        }
    }
    static const wchar_t *PRE[4] = { L"ultrafast", L"superfast", L"veryfast", L"faster" };
    if (useAudio) {
        _snwprintf(ain, 419, L"-thread_queue_size 1024 -f %s -ar %d -ac %d -i %s ", aInfo.fmt, aInfo.rate, aInfo.ch, capPipeName); ain[419] = 0;
        _snwprintf(aout, 119, L"-c:a aac -b:a %dk -ac 2 -ar 48000 ", cc.abr); aout[119] = 0;
    }
    ff_path(ffp); ff_dpi_shim(ffp);
    _snwprintf(cl, 3999,
        L"\"%s\" -hide_banner -y -loglevel warning -nostats %s"
        L"-thread_queue_size 1024 -f gdigrab -framerate %d -draw_mouse %d -offset_x %d -offset_y %d -video_size %dx%d -rtbufsize 256M -i desktop "
        L"-map %d:v %s-c:v libx265 -preset %s -crf %d -pix_fmt yuv420p -x265-params log-level=error %s-fps_mode cfr -r %d %s\"%s\"",
        ffp, ain, cc.fps, cc.cursor ? 1 : 0, (int)rg.left, (int)rg.top, (int)(rg.right - rg.left), (int)(rg.bottom - rg.top),
        useAudio ? 1 : 0, useAudio ? L"-map 0:a " : L"", PRE[cc.speed], cc.crf, cc.fmt ? L"-tag:v hvc1 " : L"", cc.fps, aout, capCurOut);
    cl[3999] = 0;
    SECURITY_ATTRIBUTES sa = { sizeof sa, NULL, TRUE }; HANDLE inR = NULL, inW = NULL, erR = NULL, erW = NULL;
    if (!CreatePipe(&inR, &inW, &sa, 0) || !CreatePipe(&erR, &erW, &sa, 0)) { cap_set_status(L"Impossible de créer les tubes de communication.", C_RED); audio_stop(); cap_free_events(); return; }
    SetHandleInformation(inW, HANDLE_FLAG_INHERIT, 0); SetHandleInformation(erR, HANDLE_FLAG_INHERIT, 0);
    STARTUPINFOW si; memset(&si, 0, sizeof si); si.cb = sizeof si; si.dwFlags = STARTF_USESTDHANDLES; si.hStdInput = inR; si.hStdOutput = erW; si.hStdError = erW;
    PROCESS_INFORMATION pi; memset(&pi, 0, sizeof pi);
    BOOL ok = CreateProcessW(NULL, cl, NULL, NULL, TRUE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi);
    CloseHandle(inR); CloseHandle(erW);
    if (!ok) { CloseHandle(inW); CloseHandle(erR); audio_stop(); cap_free_events(); cap_set_status(L"Impossible de lancer FFmpeg.", C_RED); return; }
    CloseHandle(pi.hThread); capProc = pi.hProcess; capIn = inW; capErrR = erR; capErr[0] = 0;
    capErrThr = CreateThread(NULL, 0, cap_err_thread, NULL, 0, NULL);
    if (useAudio) SetEvent(aEvGo);
    capRunning = 1; capStopping = 0; capT0 = GetTickCount(); capLast[0] = 0;
    cap_set_status(L"● Enregistrement en cours…", C_RED);
    if (!SetWindowDisplayAffinity(hCap, WDA_EXCLUDEFROMCAPTURE)) ShowWindow(hCap, SW_MINIMIZE);    /* anciens Windows : la fenetre ne peut pas etre masquee de la capture */
    SetTimer(hCap, 2, 500, NULL); inval();
}

static DWORD WINAPI cap_stop_thread(LPVOID a) {
    (void)a; DWORD w;
    if (capIn) WriteFile(capIn, "q", 1, &w, NULL);                        /* arret propre : FFmpeg termine le fichier */
    audio_stop();
    if (WaitForSingleObject(capProc, 30000) != WAIT_OBJECT_0) TerminateProcess(capProc, 1);
    if (hCap) PostMessage(hCap, WM_CAP_DONE, 0, 0);
    return 0;
}
static void cap_stop(void) {
    if (!capRunning || capStopping) return;
    capStopping = 1; cap_set_status(L"Finalisation du fichier…", C_ACC);
    capStopThr = CreateThread(NULL, 0, cap_stop_thread, NULL, 0, NULL);
}

static void cap_finish(int fromError) {
    audio_stop();
    if (capIn) { CloseHandle(capIn); capIn = NULL; }
    if (capErrThr) { WaitForSingleObject(capErrThr, 1500); CloseHandle(capErrThr); capErrThr = NULL; }
    if (capErrR) { CloseHandle(capErrR); capErrR = NULL; }
    DWORD ec = 0; if (capProc) { GetExitCodeProcess(capProc, &ec); CloseHandle(capProc); capProc = NULL; }
    cap_free_events();
    int stopped = capStopping;
    if (hCap) KillTimer(hCap, 2);
    capRunning = 0; capStopping = 0;
    WIN32_FILE_ATTRIBUTE_DATA fa; int has = GetFileAttributesExW(capCurOut, GetFileExInfoStandard, &fa) && (fa.nFileSizeHigh || fa.nFileSizeLow > 2048);
    if (has && (stopped || ec == 0)) {
        double mo = (fa.nFileSizeHigh * 4294967296.0 + fa.nFileSizeLow) / 1048576.0; wchar_t m[420];
        const wchar_t *nm = wcsrchr(capCurOut, L'\\'); nm = nm ? nm + 1 : capCurOut;
        wcscpy(capLast, capCurOut); _snwprintf(m, 419, L"✔ Enregistré : %s   (%.1f Mo)", nm, mo); m[419] = 0; cap_set_status(m, RGB(60, 200, 90));
    } else {
        wchar_t m[420], e[400] = L""; char tail[360];
        EnterCriticalSection(&csErr); { size_t l = strlen(capErr); const char *p = capErr + (l > 340 ? l - 340 : 0); strncpy(tail, p, 359); tail[359] = 0; } LeaveCriticalSection(&csErr);
        for (char *q = tail; *q; q++) if (*q == '\r' || *q == '\n') *q = ' ';
        u8w(tail, e, 400);
        if (e[0]) _snwprintf(m, 419, L"FFmpeg s'est arrêté : %s", e); else _snwprintf(m, 419, L"FFmpeg s'est arrêté (code %lu).", ec);
        m[419] = 0; cap_set_status(m, C_RED); (void)fromError;
    }
    if (hCap) { SetWindowDisplayAffinity(hCap, 0); InvalidateRect(hCap, NULL, FALSE); }
    inval();
}

static void cap_shutdown(void) {              /* fermeture du lecteur pendant un enregistrement : on termine proprement le fichier */
    if (!capRunning || !capProc) return;
    if (capStopThr) WaitForSingleObject(capStopThr, 35000);
    else { DWORD w; if (capIn) WriteFile(capIn, "q", 1, &w, NULL); capStopping = 1; audio_stop(); if (WaitForSingleObject(capProc, 30000) != WAIT_OBJECT_0) TerminateProcess(capProc, 1); }
    if (capRunning) cap_finish(0);
}

/* ----- fenetre de capture (dessinee a la main, style du lecteur) ----- */
enum { R_M0, R_M1, R_M2, R_TARGET, R_ZONE, R_S0, R_S1, R_S2, R_S3, R_AUD, R_CUR, R_MKV, R_MP4, R_OUT, R_BROWSE, R_DESK, R_REC, R_OPEN, R_PLAY, R_CLOSE, R_N };
static RECT capR[R_N];
#define CAP_W 640
#define CAP_H 568
static const struct { const wchar_t *name; int lo, hi, step, inv; } SLD[4] = {
    { L"Qualité vidéo (x265)", 18, 34, 1, 1 }, { L"Images par seconde", 10, 60, 5, 0 },
    { L"Qualité audio (AAC)", 64, 320, 16, 0 }, { L"Vitesse d'encodage", 0, 3, 1, 0 } };
static int *sld_val(int k) { return k == 0 ? &cc.crf : k == 1 ? &cc.fps : k == 2 ? &cc.abr : &cc.speed; }
static void sld_text(int k, wchar_t *o) {
    int v = *sld_val(k);
    if (k == 0) { const wchar_t *q = v <= 20 ? L"Très haute" : v <= 24 ? L"Haute" : v <= 28 ? L"Standard" : v <= 31 ? L"Économique" : L"Légère"; _snwprintf(o, 59, L"%s · CRF %d", q, v); }
    else if (k == 1) _snwprintf(o, 59, L"%d i/s", v);
    else if (k == 2) _snwprintf(o, 59, L"%d kb/s", v);
    else { static const wchar_t *n[4] = { L"Ultra-rapide · CPU faible", L"Rapide", L"Équilibré", L"Qualité · CPU élevé" }; wcscpy(o, n[v]); }
    o[59] = 0;
}
static void sld_set(int k, int x) {
    RECT r = capR[R_S0 + k]; double f = (double)(x - r.left) / (double)(r.right - r.left); if (f < 0) f = 0; if (f > 1) f = 1;
    if (SLD[k].inv) f = 1 - f;
    int st = SLD[k].step, v = SLD[k].lo + (int)(f * (SLD[k].hi - SLD[k].lo) + st / 2.0); v = SLD[k].lo + (v - SLD[k].lo) / st * st;
    *sld_val(k) = clampi(v, SLD[k].lo, SLD[k].hi);
}

static void cap_layout(void) {
    int W = S(CAP_W), pad = S(22), g = S(6), x0 = pad, x1 = W - pad, y, tw = (x1 - x0 - 2 * g) / 3;
    for (int i = 0; i < 3; i++) SetRect(&capR[R_M0 + i], x0 + i * (tw + g), S(38), x0 + i * (tw + g) + tw, S(74));
    y = S(84);
    if (cc.mode == CM_ZONE) { SetRect(&capR[R_TARGET], x0, y, x1 - S(156), y + S(34)); SetRect(&capR[R_ZONE], x1 - S(150), y, x1, y + S(34)); }
    else { SetRect(&capR[R_TARGET], x0, y, x1, y + S(34)); SetRectEmpty(&capR[R_ZONE]); }
    for (int k = 0; k < 4; k++) { int yy = S(158) + k * S(40); SetRect(&capR[R_S0 + k], x0 + S(190), yy + S(10), x1 - S(176), yy + S(26)); }
    int ow = (x1 - x0 - 3 * g) / 4; y = S(330);
    for (int i = 0; i < 4; i++) SetRect(&capR[R_AUD + i], x0 + i * (ow + g), y, x0 + i * (ow + g) + ow, y + S(34));
    y = S(402); SetRect(&capR[R_DESK], x1 - S(76), y, x1, y + S(34)); SetRect(&capR[R_BROWSE], capR[R_DESK].left - g - S(104), y, capR[R_DESK].left - g, y + S(34));
    SetRect(&capR[R_OUT], x0, y, capR[R_BROWSE].left - g, y + S(34));
    y = S(512); SetRect(&capR[R_REC], x0, y, x0 + S(210), y + S(40)); SetRect(&capR[R_CLOSE], x1 - S(110), y, x1, y + S(40));
    if (capLast[0] && !capRunning) { SetRect(&capR[R_PLAY], capR[R_CLOSE].left - g - S(90), y, capR[R_CLOSE].left - g, y + S(40)); SetRect(&capR[R_OPEN], capR[R_PLAY].left - g - S(150), y, capR[R_PLAY].left - g, y + S(40)); }
    else { SetRectEmpty(&capR[R_PLAY]); SetRectEmpty(&capR[R_OPEN]); }
}
static int cap_hit(int x, int y) {
    POINT p = { x, y };
    for (int i = 0; i < R_N; i++) {
        RECT r = capR[i]; if (IsRectEmpty(&r)) continue;
        if (i >= R_S0 && i <= R_S3) InflateRect(&r, S(8), S(8));
        if (PtInRect(&r, p)) return i;
    }
    return -1;
}
static int cap_target_text(wchar_t *o) {                  /* renvoie 1 si c'est un texte d'invite (grise) */
    if (cc.mode == CM_SCREEN) { if (capMon <= 0 || capMon > nMons) wcscpy(o, L"Tous les écrans (bureau complet)"); else wcscpy(o, mons[capMon - 1].name); return 0; }
    if (cc.mode == CM_ZONE) {
        if (!cc.hasZone) { wcscpy(o, L"Aucune zone — cliquez sur « Choisir la zone… »"); return 1; }
        _snwprintf(o, 199, L"Zone : %d × %d px   à (%d, %d)", (int)(cc.zone.right - cc.zone.left), (int)(cc.zone.bottom - cc.zone.top), (int)cc.zone.left, (int)cc.zone.top); o[199] = 0; return 0;
    }
    if (capWin && IsWindow(capWin)) { GetWindowTextW(capWin, o, 190); return 0; }
    wcscpy(o, L"Choisir une fenêtre…"); return 1;
}

static void cap_tog(HDC dc, int id, const wchar_t *t, int on, int check, int dis) {
    RECT r = capR[id]; int hv = capHover == id && !dis;
    fill(dc, &r, hv ? C_TROU : (on && !check ? C_TROU : C_HOT));
    if (on && !check) frect(dc, r.left, r.bottom - 2, r.right, r.bottom, dis ? C_DIM : C_ACC);
    RECT x = r; COLORREF tc = dis ? C_DIM : (on && !check ? C_ACC : C_FG);
    if (check) {
        int bx = r.left + S(12), by = (r.top + r.bottom) / 2; frect(dc, bx, by - S(7), bx + S(14), by + S(7), on ? (dis ? C_DIM : C_ACC) : C_TROU);
        if (on) { HPEN pn = CreatePen(PS_SOLID, S(2), C_BG), op = SelectObject(dc, pn); MoveToEx(dc, bx + S(3), by, NULL); LineTo(dc, bx + S(6), by + S(3)); LineTo(dc, bx + S(11), by - S(3)); SelectObject(dc, op); DeleteObject(pn); }
        x.left = bx + S(22); text(dc, t, &x, tc, fUI, DT_LEFT);
    } else text(dc, t, &x, tc, fUI, DT_CENTER);
}
static void cap_chip(HDC dc, int id, const wchar_t *t, int dim, int dis, int arrow) {
    RECT r = capR[id]; fill(dc, &r, capHover == id && !dis ? C_TROU : C_HOT);
    RECT x = r; x.left += S(10); x.right -= arrow ? S(26) : S(10); text(dc, t, &x, (dim || dis) ? C_DIM : C_FG, fUI, DT_LEFT | DT_END_ELLIPSIS);
    if (arrow) { int cx = r.right - S(14), cy = (r.top + r.bottom) / 2; POINT p[3] = { { cx - S(4), cy - S(2) }, { cx + S(4), cy - S(2) }, { cx, cy + S(3) } }; poly(dc, p, 3, dis ? C_DIM : C_ACC); }
}

static void cap_paint(HDC dc, int W, int H) {
    RECT all = { 0, 0, W, H }; fill(dc, &all, C_BAR); cap_layout();
    int busy = capRunning, pad = S(22); RECT t; wchar_t b[260];
    SetRect(&t, pad, S(14), W - pad, S(34)); text(dc, L"SOURCE", &t, C_DIM, fSmall, DT_LEFT);
    const wchar_t *mn[3] = { L"Écran", L"Zone libre", L"Fenêtre" };
    for (int i = 0; i < 3; i++) cap_tog(dc, R_M0 + i, mn[i], cc.mode == i, 0, busy);
    int dim = cap_target_text(b);
    if (cc.mode == CM_ZONE) { cap_chip(dc, R_TARGET, b, dim, busy, 0); cap_tog(dc, R_ZONE, L"Choisir la zone…", 0, 0, busy); }
    else cap_chip(dc, R_TARGET, b, dim, busy, 1);
    SetRect(&t, pad, S(134), W - pad, S(154)); text(dc, L"QUALITÉ", &t, C_DIM, fSmall, DT_LEFT);
    for (int k = 0; k < 4; k++) {
        RECT tr = capR[R_S0 + k]; int cy = (tr.top + tr.bottom) / 2; RECT nl = { pad, cy - S(12), pad + S(184), cy + S(12) }, vl = { tr.right + S(14), cy - S(12), W - pad, cy + S(12) };
        text(dc, SLD[k].name, &nl, busy ? C_DIM : C_FG, fUI, DT_LEFT);
        double f = (double)(*sld_val(k) - SLD[k].lo) / (double)(SLD[k].hi - SLD[k].lo); if (SLD[k].inv) f = 1 - f;
        bar(dc, &tr, f, busy ? C_DIM : C_ACC, S(3), S(6));
        sld_text(k, b); text(dc, b, &vl, busy ? C_DIM : C_ACC, fUI, DT_LEFT | DT_END_ELLIPSIS);
    }
    cap_tog(dc, R_AUD, L"Son du PC", cc.audio, 1, busy); cap_tog(dc, R_CUR, L"Curseur souris", cc.cursor, 1, busy);
    cap_tog(dc, R_MKV, L"MKV", !cc.fmt, 0, busy); cap_tog(dc, R_MP4, L"MP4", cc.fmt, 0, busy);
    SetRect(&t, pad, S(378), W - pad, S(398)); text(dc, L"DOSSIER DE SORTIE", &t, C_DIM, fSmall, DT_LEFT);
    cap_chip(dc, R_OUT, cc.outdir, 0, busy, 0); cap_tog(dc, R_BROWSE, L"Parcourir…", 0, 0, busy); cap_tog(dc, R_DESK, L"Bureau", 0, 0, busy);
    SetRect(&t, pad, S(448), W - pad, S(500));
    { wchar_t s[440]; wcscpy(s, capStatus[0] ? capStatus : L"Prêt. Choisissez la source, réglez la qualité puis cliquez sur Enregistrer.");
      if (capRunning && !capStopping) { DWORD e = (GetTickCount() - capT0) / 1000; const wchar_t *nm = wcsrchr(capCurOut, L'\\'); nm = nm ? nm + 1 : capCurOut;
          _snwprintf(s, 439, L"● Enregistrement en cours   %02lu:%02lu:%02lu   ·   %s", e / 3600, (e / 60) % 60, e % 60, nm); s[439] = 0; }
      SetBkMode(dc, TRANSPARENT); SetTextColor(dc, capRunning ? C_RED : (capStatus[0] ? capStatusClr : C_DIM)); SelectObject(dc, fUI);
      DrawTextW(dc, s, -1, &t, DT_LEFT | DT_WORDBREAK | DT_NOPREFIX | DT_END_ELLIPSIS); }
    /* boutons d'action */
    { RECT r = capR[R_REC]; int dis = capStopping; fill(dc, &r, capHover == R_REC && !dis ? C_TROU : C_HOT);
      frect(dc, r.left, r.bottom - 2, r.right, r.bottom, dis ? C_DIM : (capRunning ? C_RED : C_ACC));
      int cx = r.left + S(30), cy = (r.top + r.bottom) / 2;
      if (capRunning) frect(dc, cx - S(6), cy - S(6), cx + S(6), cy + S(6), dis ? C_DIM : C_RED);
      else { SetDCBrushColor(dc, C_RED); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN)); Ellipse(dc, cx - S(7), cy - S(7), cx + S(7), cy + S(7)); }
      RECT x = r; x.left += S(50); text(dc, capStopping ? L"Finalisation…" : (capRunning ? L"Arrêter" : L"Enregistrer"), &x, dis ? C_DIM : C_FG, fUI, DT_LEFT); }
    cap_tog(dc, R_CLOSE, L"Fermer", 0, 0, 0);
    if (capLast[0] && !capRunning) { cap_tog(dc, R_OPEN, L"Ouvrir le dossier", 0, 0, 0); cap_tog(dc, R_PLAY, L"Lire", 0, 0, 0); }
}

static void cap_screen_menu(void) {
    mons_refresh(); HMENU m = CreatePopupMenu();
    AppendMenuW(m, MF_STRING | (capMon == 0 ? MF_CHECKED : 0), 100, L"Tous les écrans (bureau complet)"); AppendMenuW(m, MF_SEPARATOR, 0, NULL);
    for (int i = 0; i < nMons; i++) AppendMenuW(m, MF_STRING | (capMon == i + 1 ? MF_CHECKED : 0), 101 + i, mons[i].name);
    POINT p = { capR[R_TARGET].left, capR[R_TARGET].bottom }; ClientToScreen(hCap, &p);
    int c = TrackPopupMenu(m, TPM_LEFTALIGN | TPM_TOPALIGN | TPM_RETURNCMD, p.x, p.y, 0, hCap, NULL); DestroyMenu(m);
    if (c >= 100) { capMon = c - 100; cap_save(); }
}
static void cap_window_menu(void) {
    nWl = 0; EnumWindows(win_cb, 0); HMENU m = CreatePopupMenu();
    for (int i = 0; i < nWl; i++) { wchar_t e[170]; esc_amp(wl[i].t, e, 170); AppendMenuW(m, MF_STRING | (wl[i].h == capWin ? MF_CHECKED : 0), 200 + i, e); }
    if (!nWl) AppendMenuW(m, MF_STRING | MF_GRAYED, 0, L"Aucune fenêtre disponible");
    POINT p = { capR[R_TARGET].left, capR[R_TARGET].bottom }; ClientToScreen(hCap, &p);
    int c = TrackPopupMenu(m, TPM_LEFTALIGN | TPM_TOPALIGN | TPM_RETURNCMD, p.x, p.y, 0, hCap, NULL); DestroyMenu(m);
    if (c >= 200 && c < 200 + nWl) capWin = wl[c - 200].h;
}
static void cap_browse(void) {
    BROWSEINFOW bi; memset(&bi, 0, sizeof bi); bi.hwndOwner = hCap; bi.lpszTitle = L"Dossier de sortie des captures"; bi.ulFlags = BIF_RETURNONLYFSDIRS | BIF_NEWDIALOGSTYLE;
    LPITEMIDLIST pl = SHBrowseForFolderW(&bi);
    if (pl) { wchar_t p[MAX_PATH]; if (SHGetPathFromIDListW(pl, p)) { wcscpy(cc.outdir, p); cap_save(); } CoTaskMemFree(pl); }
}

static LRESULT CALLBACK CapProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT rc; GetClientRect(h, &rc);
        HDC md = CreateCompatibleDC(dc); HBITMAP bm = CreateCompatibleBitmap(dc, rc.right, rc.bottom); HGDIOBJ old = SelectObject(md, bm);
        cap_paint(md, rc.right, rc.bottom); BitBlt(dc, 0, 0, rc.right, rc.bottom, md, 0, 0, SRCCOPY);
        SelectObject(md, old); DeleteObject(bm); DeleteDC(md); EndPaint(h, &ps); return 0; }
    case WM_MOUSEMOVE: {
        int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
        if (capDrag >= 0) { sld_set(capDrag, x); InvalidateRect(h, NULL, FALSE); }
        else { int nh = cap_hit(x, y); if (nh != capHover) { capHover = nh; InvalidateRect(h, NULL, FALSE); } TRACKMOUSEEVENT t = { sizeof t, TME_LEAVE, h, 0 }; TrackMouseEvent(&t); }
        return 0; }
    case WM_MOUSELEAVE: capHover = -1; InvalidateRect(h, NULL, FALSE); return 0;
    case WM_LBUTTONDOWN: {
        int id = cap_hit(GET_X_LPARAM(lp), GET_Y_LPARAM(lp)); if (id < 0) return 0;
        int locked = capRunning && id != R_REC && id != R_CLOSE;
        if (locked) return 0;
        switch (id) {
        case R_M0: case R_M1: case R_M2: cc.mode = id - R_M0; cap_save(); break;
        case R_TARGET: if (cc.mode == CM_SCREEN) cap_screen_menu(); else if (cc.mode == CM_WINDOW) cap_window_menu(); else cap_pick_zone(); break;
        case R_ZONE: cap_pick_zone(); break;
        case R_S0: case R_S1: case R_S2: case R_S3: capDrag = id - R_S0; SetCapture(h); sld_set(capDrag, GET_X_LPARAM(lp)); break;
        case R_AUD: cc.audio = !cc.audio; cap_save(); break;
        case R_CUR: cc.cursor = !cc.cursor; cap_save(); break;
        case R_MKV: cc.fmt = 0; cap_save(); break;
        case R_MP4: cc.fmt = 1; cap_save(); break;
        case R_OUT: case R_BROWSE: cap_browse(); break;
        case R_DESK: desktop_dir(cc.outdir); cap_save(); break;
        case R_REC: if (!capRunning) cap_start(); else cap_stop(); break;
        case R_OPEN: { wchar_t a[MAX_PATH + 20]; _snwprintf(a, MAX_PATH + 19, L"/select,\"%s\"", capLast); a[MAX_PATH + 19] = 0; ShellExecuteW(NULL, L"open", L"explorer.exe", a, NULL, SW_SHOWNORMAL); } break;
        case R_PLAY: if (mpv) { load_file(capLast); ShowWindow(hMain, SW_RESTORE); SetForegroundWindow(hMain); } break;
        case R_CLOSE: SendMessage(h, WM_CLOSE, 0, 0); return 0;
        }
        InvalidateRect(h, NULL, FALSE); return 0; }
    case WM_LBUTTONUP: if (capDrag >= 0) { capDrag = -1; ReleaseCapture(); cap_save(); InvalidateRect(h, NULL, FALSE); } return 0;
    case WM_TIMER:
        if (wp == 2 && capRunning) {
            if (!capStopping && capProc && WaitForSingleObject(capProc, 0) == WAIT_OBJECT_0) cap_finish(1);   /* FFmpeg s'est arrete tout seul */
            else { InvalidateRect(h, NULL, FALSE); inval(); }
        }
        return 0;
    case WM_CAP_DONE:
        if (capStopThr) { CloseHandle(capStopThr); capStopThr = NULL; }
        cap_finish(0); if (capCloseAfter) { capCloseAfter = 0; DestroyWindow(h); }
        return 0;
    case WM_CLOSE:
        if (capRunning) { capCloseAfter = 1; cap_stop(); return 0; }
        DestroyWindow(h); return 0;
    case WM_DESTROY: hCap = NULL; return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

static void capture_window(void) {
    static int reg = 0;
    if (hCap) { if (IsIconic(hCap)) ShowWindow(hCap, SW_RESTORE); SetForegroundWindow(hCap); return; }
    if (!reg) {
        if (!brDlg) { brDlg = CreateSolidBrush(C_BAR); brEdit = CreateSolidBrush(C_BG); }
        WNDCLASSW wc; memset(&wc, 0, sizeof wc); wc.lpfnWndProc = CapProc; wc.hInstance = hInst; wc.lpszClassName = L"LavCap";
        wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hIcon = LoadIconW(hInst, MAKEINTRESOURCEW(1)); RegisterClassW(&wc); reg = 1;
    }
    cap_load(); mons_refresh(); capStatus[0] = 0; capLast[0] = 0;
    DWORD st = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX; RECT r = { 0, 0, S(CAP_W), S(CAP_H) }; AdjustWindowRectEx(&r, st, FALSE, 0);
    RECT mr; GetWindowRect(hMain, &mr); int w = r.right - r.left, hh = r.bottom - r.top;
    hCap = CreateWindowExW(0, L"LavCap", L"Capture écran", st, mr.left + ((mr.right - mr.left) - w) / 2, mr.top + ((mr.bottom - mr.top) - hh) / 2, w, hh, NULL, NULL, hInst, NULL);
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute"); if (f) { f(hCap, 20, &dark, sizeof dark); f(hCap, 19, &dark, sizeof dark); } }
    ShowWindow(hCap, SW_SHOW); SetForegroundWindow(hCap);
}

static int install_window(int needMpv, int needFf, int ask);
static void capture_open(void) {
    if (!ff_present()) {
        if (install_window(0, 1, 1) != 1 || !ff_present()) return;
    }
    capture_window();
}


/* ================= fond anime pour les flux audio : vagues qui suivent la musique ================= */
#define VB 48
static float vizBands[VB], vizLvl; static volatile int vizStop, vizFallback; static HANDLE vizThr;
static wchar_t vizTitle[256];

static void viz_analyze(const float *blk, const float *coef, const float *win) {
    float tmp[2048]; double e = 0;
    for (int i = 0; i < 2048; i++) { tmp[i] = blk[i] * win[i]; e += blk[i] * blk[i]; }
    float rms = sqrtf((float)(e / 2048.0)); float lv = rms * 4.0f; if (lv > 1) lv = 1;
    vizLvl += (lv - vizLvl) * (lv > vizLvl ? 0.6f : 0.15f);
    for (int k = 0; k < VB; k++) {
        float s1 = 0, s2 = 0, c = coef[k];
        for (int i = 0; i < 2048; i++) { float s0 = tmp[i] + c * s1 - s2; s2 = s1; s1 = s0; }
        float pw = s1 * s1 + s2 * s2 - c * s1 * s2; if (pw < 0) pw = 0;
        float amp = sqrtf(pw) * 4.0f / 2048.0f;
        float v = (20.0f * log10f(amp + 1e-6f) + 62.0f) / 50.0f; if (v < 0) v = 0; if (v > 1) v = 1;
        vizBands[k] += (v - vizBands[k]) * (v > vizBands[k] ? 0.55f : 0.12f);
    }
}

static DWORD WINAPI viz_thread(LPVOID a) {
    (void)a;
    IMMDeviceEnumerator *en = NULL; IMMDevice *dev = NULL; IAudioClient *ac = NULL; IAudioCaptureClient *cl = NULL; WAVEFORMATEX *wf = NULL;
    int started = 0, isF = 0, ch = 2, rate = 48000; HRESULT hr;
    static float win[2048]; float coef[VB], blk[2048]; int nb = 0;
    CoInitializeEx(NULL, COINIT_MULTITHREADED);
    hr = CoCreateInstance(&G_CLSID_MMDevEnum, NULL, CLSCTX_ALL, &G_IID_IMMDevEnum, (void **)&en);
    if (SUCCEEDED(hr)) hr = IMMDeviceEnumerator_GetDefaultAudioEndpoint(en, eRender, eConsole, &dev);
    if (SUCCEEDED(hr)) hr = IMMDevice_Activate(dev, &G_IID_IAudioClient, CLSCTX_ALL, NULL, (void **)&ac);
    if (SUCCEEDED(hr)) hr = IAudioClient_GetMixFormat(ac, &wf);
    if (SUCCEEDED(hr)) {
        int isP = wf->wFormatTag == WAVE_FORMAT_PCM; isF = wf->wFormatTag == WAVE_FORMAT_IEEE_FLOAT;
        if (wf->wFormatTag == WAVE_FORMAT_EXTENSIBLE) { WAVEFORMATEXTENSIBLE *we = (WAVEFORMATEXTENSIBLE *)wf; isF = IsEqualGUID(&we->SubFormat, &G_SUB_FLOAT); isP = IsEqualGUID(&we->SubFormat, &G_SUB_PCM); }
        ch = wf->nChannels; rate = (int)wf->nSamplesPerSec;
        if (ch < 1 || !((isF && wf->wBitsPerSample == 32) || (isP && wf->wBitsPerSample == 16))) hr = E_FAIL;
        else hr = IAudioClient_Initialize(ac, AUDCLNT_SHAREMODE_SHARED, AUDCLNT_STREAMFLAGS_LOOPBACK, 10000000, 0, wf, NULL);
    }
    if (SUCCEEDED(hr)) hr = IAudioClient_GetService(ac, &G_IID_IACapture, (void **)&cl);
    if (FAILED(hr)) { vizFallback = 1; goto out; }
    vizFallback = 0;
    for (int i = 0; i < 2048; i++) win[i] = 0.5f - 0.5f * cosf(2.0f * 3.14159265f * i / 2047.0f);
    for (int k = 0; k < VB; k++) { float f = 40.0f * powf(12000.0f / 40.0f, (float)k / (VB - 1)); if (f > rate * 0.45f) f = rate * 0.45f; coef[k] = 2.0f * cosf(2.0f * 3.14159265f * f / rate); }
    IAudioClient_Start(ac); started = 1;
    while (!vizStop) {
        UINT32 np = 0; int got = 0;
        while (!vizStop && SUCCEEDED(IAudioCaptureClient_GetNextPacketSize(cl, &np)) && np) {
            BYTE *d = NULL; UINT32 n = 0; DWORD fl = 0;
            if (FAILED(IAudioCaptureClient_GetBuffer(cl, &d, &n, &fl, NULL, NULL))) break;
            UINT32 nf = n; got = 1;
            for (UINT32 i = 0; i < n; i++) {
                float s = 0;
                if (!(fl & AUDCLNT_BUFFERFLAGS_SILENT)) { for (int c = 0; c < ch; c++) s += isF ? ((float *)d)[i * ch + c] : ((short *)d)[i * ch + c] / 32768.0f; s /= ch; }
                blk[nb++] = s;
                if (nb == 2048) { viz_analyze(blk, coef, win); memmove(blk, blk + 1024, 1024 * sizeof(float)); nb = 1024; }
            }
            IAudioCaptureClient_ReleaseBuffer(cl, nf);
        }
        if (!got) { for (int k = 0; k < VB; k++) vizBands[k] *= 0.9f; vizLvl *= 0.9f; }
        Sleep(10);
    }
out:
    if (started) IAudioClient_Stop(ac);
    if (cl) IAudioCaptureClient_Release(cl);
    if (ac) IAudioClient_Release(ac);
    if (dev) IMMDevice_Release(dev);
    if (en) IMMDeviceEnumerator_Release(en);
    if (wf) CoTaskMemFree(wf);
    CoUninitialize();
    return 0;
}

static void viz_apply(void) {
    if (vizOn) {
        if (vizThr && WaitForSingleObject(vizThr, 0) == WAIT_OBJECT_0) { CloseHandle(vizThr); vizThr = NULL; }
        if (!vizThr) { vizStop = 0; vizThr = CreateThread(NULL, 0, viz_thread, NULL, 0, NULL); }
        vizTitle[0] = 0;
        if (chanTitle[0]) wcsncpy(vizTitle, chanTitle, 255);
        else { char *t = p_get_property_string(mpv, "media-title"); if (t) { u8w(t, vizTitle, 256); p_free(t); } }
        SetTimer(hViz, 3, 33, NULL);
    } else {
        KillTimer(hViz, 3); vizStop = 1;
        if (vizThr) { WaitForSingleObject(vizThr, 1500); CloseHandle(vizThr); vizThr = NULL; }
    }
    do_layout();
}
static void viz_update(int realVideo) {
    int on = playing && nAud > 0 && !realVideo;
    if (on != vizOn) { vizOn = on; viz_apply(); }
}

static COLORREF mixc(COLORREF a, COLORREF b, double f) {
    if (f < 0) f = 0; if (f > 1) f = 1;
    return RGB((int)(GetRValue(a) + (GetRValue(b) - GetRValue(a)) * f), (int)(GetGValue(a) + (GetGValue(b) - GetGValue(a)) * f), (int)(GetBValue(a) + (GetBValue(b) - GetBValue(a)) * f));
}
static COLORREF viz_bg(int y, int h) { double k = (double)y / (h ? h : 1); return RGB((int)(3 + 5 * k), (int)(9 + 27 * k), (int)(22 + 54 * k)); }
typedef struct { float x, y, r, vy, vx, ph, a; int on, fillc; } Bub;
static Bub bub[56]; static DWORD bubT; static unsigned rngs = 2463534242u; static float prevBass;
static float rndf(void) { rngs ^= rngs << 13; rngs ^= rngs >> 17; rngs ^= rngs << 5; return (rngs & 0xFFFFFF) / 16777216.0f; }
static double rib_cy(int h, double u, double t, double m, double bass) {
    double sm = u * u * (3 - 2 * u);                                   /* S-curve : monte de gauche a droite */
    return h * (0.74 - 0.24 * sm) + sin(u * 7.0 + t * 1.1) * h * 0.012 * (1 + 3 * bass) - m * h * 0.075;
}

static void draw_viz_gdi(HDC dc, int w, int h) {
    double t = GetTickCount() / 1000.0; const COLORREF ACC = RGB(23, 147, 209), LIGHT = RGB(125, 207, 255);
    float bands[VB], lv = vizLvl, bass = 0, mid = 0, hi = 0;
    for (int k = 0; k < VB; k++) bands[k] = vizFallback ? (float)(0.25 + 0.2 * sin(t * 2.0 + k * 0.4)) : vizBands[k];
    if (vizFallback) lv = (float)(0.35 + 0.15 * sin(t * 1.3));
    for (int k = 0; k < 8; k++) bass += bands[k] / 8; for (int k = 8; k < 26; k++) mid += bands[k] / 18; for (int k = 26; k < VB; k++) hi += bands[k] / (VB - 26);
    /* fond : degrade sombre + fines lignes (aspect brosse) */
    for (int y = 0; y < h; y += 2) { COLORREF c = viz_bg(y, h); if ((y / 2) & 1) c = RGB(GetRValue(c) + 2, GetGValue(c) + 2, GetBValue(c) + 2); frect(dc, 0, y, w, y + 2, c); }
    int step = (w + 179) / 180; if (step < 4) step = 4;
    static POINT pa[420], pb[420];
    /* grandes courbes douces en arriere-plan */
    for (int j = 0; j < 2; j++) {
        int n = 0;
        for (int x = 0; x <= w + step; x += step) {
            double u = (double)(x > w ? w : x) / (w ? w : 1);
            double y = h * (0.52 - 0.30 * u * u * (3 - 2 * u) - 0.10 * j) + sin(u * 3.0 + t * 0.15 + j) * h * 0.02;
            pa[n].x = x; pa[n].y = (LONG)y; if (++n >= 414) break;
        }
        pa[n].x = w; pa[n].y = 0; pa[n + 1].x = 0; pa[n + 1].y = 0;
        poly(dc, pa, n + 2, j ? RGB(10, 30, 62) : RGB(8, 24, 52));
    }
    /* bulles : mise a jour */
    { DWORD now = GetTickCount(); float dt = bubT ? (now - bubT) / 1000.0f : 0.03f; bubT = now; if (dt > 0.1f) dt = 0.1f;
      int spawn = 0; if (bass - prevBass > 0.08f && bass > 0.3f) spawn += 3 + (int)(bass * 4); prevBass = bass;
      if (rndf() < (0.10f + 0.9f * lv) * dt * 30.0f) spawn++;
      for (int s = 0; s < spawn; s++) for (int i = 0; i < 56; i++) if (!bub[i].on) {
          Bub *b = &bub[i]; double u = rndf(); b->x = (float)(u * w);
          b->y = (float)(rib_cy(h, u, t, 0, bass) + (rndf() - 0.5f) * S(30)); b->r = S(3) + rndf() * S(13) * (0.6f + bass);
          b->vy = -(S(16) + rndf() * S(46)) * (0.7f + lv); b->vx = (rndf() - 0.5f) * S(18); b->ph = rndf() * 6.28f; b->a = 1; b->on = 1; b->fillc = (rndf() < 0.3f && b->r < S(8)); break; }
      for (int i = 0; i < 56; i++) if (bub[i].on) {
          Bub *b = &bub[i]; b->y += b->vy * dt; b->x += b->vx * dt + (float)sin(b->ph + t) * S(6) * dt; b->a -= dt * 0.16f;
          if (b->a <= 0 || b->y < -b->r) b->on = 0; } }
    /* ruban lumineux (halo + lignes fines) */
    { int n = 0; double cy[420], tp[420]; int xs[420];
      for (int x = 0; x <= w + step; x += step) {
          double u = (double)(x > w ? w : x) / (w ? w : 1); double bi = u * (VB - 1); int b0 = (int)bi, b1 = b0 + 1 < VB ? b0 + 1 : b0; double fr = bi - b0;
          double m = bands[b0] * (1 - fr) + bands[b1] * fr;
          cy[n] = rib_cy(h, u, t, m, bass); tp[n] = pow(sin(3.14159265 * u), 0.7) * (1 + 0.6 * lv); xs[n] = x; if (++n >= 414) break; }
      for (int g = 5; g >= 0; g--) {
          double wd = S(10) + S(10) * g * (1 + lv); int k = 0;
          for (int i = 0; i < n; i++) { pa[k].x = xs[i]; pa[k].y = (LONG)(cy[i] - wd * tp[i] * 0.5); k++; }
          for (int i = n - 1; i >= 0; i--) { pa[k].x = xs[i]; pa[k].y = (LONG)(cy[i] + wd * tp[i] * 0.5); k++; }
          poly(dc, pa, k, mixc(viz_bg((int)(h * 0.7), h), ACC, 0.05 + 0.075 * (5 - g) + 0.15 * lv * (g < 2)));
      }
      for (int l = 0; l < 7; l++) {
          double o = (l - 3) * S(4.5) * (1 + 0.8 * lv), ph = l * 0.9; int k = 0;
          for (int i = 0; i < n; i++) { pb[k].x = xs[i]; pb[k].y = (LONG)(cy[i] + o * tp[i] + sin(xs[i] * 0.011 + t * (0.7 + 0.15 * l) + ph) * S(2) * (1 + 3 * mid) * tp[i]); k++; }
          HPEN pn = CreatePen(PS_SOLID, l == 3 ? S(2) : S(1), l == 3 ? RGB(228, 246, 255) : mixc(viz_bg((int)(h * 0.7), h), LIGHT, 0.30 + 0.07 * (3 - abs(l - 3)) + 0.2 * hi)), op = SelectObject(dc, pn);
          Polyline(dc, pb, k); SelectObject(dc, op); DeleteObject(pn);
      } }
    /* bulles : dessin (anneaux lumineux + petits points pleins) */
    { SelectObject(dc, GetStockObject(NULL_BRUSH));
      for (int i = 0; i < 56; i++) if (bub[i].on) {
          Bub *b = &bub[i]; double a = b->a * (0.40 + 0.60 * (lv * 1.6 > 1 ? 1 : lv * 1.6 + 0.15)); COLORREF bg = viz_bg((int)b->y, h);
          double r = b->r * (1 + 0.25 * bass * sin(t * 6 + b->ph)); int ir = (int)r; if (ir < 2) ir = 2;
          if (b->fillc) { SetDCBrushColor(dc, mixc(bg, ACC, a)); SelectObject(dc, GetStockObject(DC_BRUSH)); SelectObject(dc, GetStockObject(NULL_PEN)); Ellipse(dc, (int)b->x - ir / 2, (int)b->y - ir / 2, (int)b->x + ir / 2, (int)b->y + ir / 2); SelectObject(dc, GetStockObject(NULL_BRUSH)); continue; }
          HPEN g1 = CreatePen(PS_SOLID, S(4), mixc(bg, ACC, a * 0.22)), g2 = CreatePen(PS_SOLID, ir > S(8) ? S(2) : S(1), mixc(bg, LIGHT, a * 0.85)), op;
          op = SelectObject(dc, g1); Ellipse(dc, (int)b->x - ir, (int)b->y - ir, (int)b->x + ir, (int)b->y + ir);
          SelectObject(dc, g2); Ellipse(dc, (int)b->x - ir, (int)b->y - ir, (int)b->x + ir, (int)b->y + ir);
          SelectObject(dc, op); DeleteObject(g1); DeleteObject(g2); } }
    /* titre */
    { static HFONT fBig; static int fd; if (!fBig || fd != dpi) { if (fBig) DeleteObject(fBig); fBig = CreateFontW(-S(36), 0, 0, 0, FW_LIGHT, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI"); fd = dpi; }
      RECT tr = { S(20), (int)(h * 0.12), w - S(20), (int)(h * 0.12) + S(56) };
      if (vizTitle[0]) text(dc, vizTitle, &tr, RGB(220, 228, 234), fBig, DT_CENTER | DT_END_ELLIPSIS);
      RECT sr = { S(20), tr.bottom, w - S(20), tr.bottom + S(24) }; text(dc, L"♪  Lecture audio", &sr, C_DIM, fUI, DT_CENTER); }
}

/* ---------- GDI+ (chargé dynamiquement) : rendu anti-crénelé du fond animé ---------- */
typedef struct { float X, Y; } GpPtF;
typedef struct { float X, Y, W, H; } GpRcF;
typedef struct { UINT32 ver; void *cb; BOOL noThr, noCodec; } GpStartIn;
#define GPA(a, r, g, b) ((DWORD)((((DWORD)(a)) << 24) | (((DWORD)(r)) << 16) | (((DWORD)(g)) << 8) | ((DWORD)(b))))
static HMODULE gpMod; static int gpOk, gpTried; static ULONG_PTR gpTok;
static int (WINAPI *pGpStart)(ULONG_PTR *, const GpStartIn *, void *);
static int (WINAPI *pGpFromHDC)(HDC, void **);
static int (WINAPI *pGpDelG)(void *);
static int (WINAPI *pGpSmooth)(void *, int);
static int (WINAPI *pGpPixOff)(void *, int);
static int (WINAPI *pGpPen)(DWORD, float, int, void **);
static int (WINAPI *pGpDelPen)(void *);
static int (WINAPI *pGpPenJoin)(void *, int);
static int (WINAPI *pGpPenCaps)(void *, int);
static int (WINAPI *pGpPenCape)(void *, int);
static int (WINAPI *pGpSolid)(DWORD, void **);
static int (WINAPI *pGpDelBr)(void *);
static int (WINAPI *pGpLines)(void *, void *, const GpPtF *, int);
static int (WINAPI *pGpCurve)(void *, void *, const GpPtF *, int);
static int (WINAPI *pGpFillPoly)(void *, void *, const GpPtF *, int, int);
static int (WINAPI *pGpFillEll)(void *, void *, float, float, float, float);
static int (WINAPI *pGpDrawEll)(void *, void *, float, float, float, float);
static int (WINAPI *pGpFillRect)(void *, void *, float, float, float, float);
static int (WINAPI *pGpLinBr)(const GpRcF *, DWORD, DWORD, int, int, void **);
static int (WINAPI *pGpPath)(int, void **);
static int (WINAPI *pGpPathEll)(void *, float, float, float, float);
static int (WINAPI *pGpDelPath)(void *);
static int (WINAPI *pGpPGrad)(void *, void **);
static int (WINAPI *pGpPGCenter)(void *, DWORD);
static int (WINAPI *pGpPGSurr)(void *, const DWORD *, int *);
static int (WINAPI *pGpFillPath)(void *, void *, void *);
static int gp_init(void) {
    if (gpTried) return gpOk; gpTried = 1;
    gpMod = LoadLibraryW(L"gdiplus.dll"); if (!gpMod) return 0;
#define LD(v, n) *(FARPROC *)&v = GetProcAddress(gpMod, n); if (!v) return 0;
    LD(pGpStart, "GdiplusStartup") LD(pGpFromHDC, "GdipCreateFromHDC") LD(pGpDelG, "GdipDeleteGraphics") LD(pGpSmooth, "GdipSetSmoothingMode")
    LD(pGpPixOff, "GdipSetPixelOffsetMode") LD(pGpPen, "GdipCreatePen1") LD(pGpDelPen, "GdipDeletePen") LD(pGpPenJoin, "GdipSetPenLineJoin")
    LD(pGpPenCaps, "GdipSetPenStartCap") LD(pGpPenCape, "GdipSetPenEndCap") LD(pGpSolid, "GdipCreateSolidFill") LD(pGpDelBr, "GdipDeleteBrush")
    LD(pGpLines, "GdipDrawLines") LD(pGpCurve, "GdipDrawCurve") LD(pGpFillPoly, "GdipFillPolygon") LD(pGpFillEll, "GdipFillEllipse")
    LD(pGpDrawEll, "GdipDrawEllipse") LD(pGpFillRect, "GdipFillRectangle") LD(pGpLinBr, "GdipCreateLineBrushFromRect")
    LD(pGpPath, "GdipCreatePath") LD(pGpPathEll, "GdipAddPathEllipse") LD(pGpDelPath, "GdipDeletePath") LD(pGpPGrad, "GdipCreatePathGradientFromPath")
    LD(pGpPGCenter, "GdipSetPathGradientCenterColor") LD(pGpPGSurr, "GdipSetPathGradientSurroundColorsWithCount") LD(pGpFillPath, "GdipFillPath")
#undef LD
    GpStartIn si = { 1, NULL, FALSE, FALSE }; if (pGpStart(&gpTok, &si, NULL) != 0) return 0;
    gpOk = 1; return 1;
}
/* palette bleue (façon fond d'écran Arch) */
#define VB_ACC   RGB(23, 147, 209)
#define VB_LIGHT RGB(125, 207, 255)
#define VB_CORE  RGB(228, 246, 255)
static void gp_pen_line(void *g, DWORD col, float wd, const GpPtF *p, int n) {
    void *pn = NULL; if (pGpPen(col, wd, 2, &pn)) return; pGpPenJoin(pn, 2); pGpPenCaps(pn, 2); pGpPenCape(pn, 2); pGpLines(g, pn, p, n); pGpDelPen(pn);
}
static void gp_fill_ell(void *g, DWORD col, float cx, float cy, float rx, float ry) {
    void *b = NULL; if (pGpSolid(col, &b)) return; pGpFillEll(g, b, cx - rx, cy - ry, rx * 2, ry * 2); pGpDelBr(b);
}
static void gp_ring(void *g, DWORD col, float wd, float cx, float cy, float r) {
    void *pn = NULL; if (pGpPen(col, wd, 2, &pn)) return; pGpDrawEll(g, pn, cx - r, cy - r, r * 2, r * 2); pGpDelPen(pn);
}
/* halo doux : dégradé radial centre -> transparent */
static void gp_glow(void *g, COLORREF c, int alpha, float cx, float cy, float rx, float ry) {
    void *path = NULL, *pg = NULL; if (pGpPath(0, &path)) return;
    pGpPathEll(path, cx - rx, cy - ry, rx * 2, ry * 2);
    if (!pGpPGrad(path, &pg)) { DWORD sur = GPA(0, GetRValue(c), GetGValue(c), GetBValue(c)); int cnt = 1;
        pGpPGCenter(pg, GPA(alpha, GetRValue(c), GetGValue(c), GetBValue(c))); pGpPGSurr(pg, &sur, &cnt); pGpFillPath(g, pg, path); pGpDelBr(pg); }
    pGpDelPath(path);
}
static void viz_title(HDC dc, int w, int h) {
    static HFONT fBig; static int fd; if (!fBig || fd != dpi) { if (fBig) DeleteObject(fBig); fBig = CreateFontW(-S(36), 0, 0, 0, FW_LIGHT, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI"); fd = dpi; }
    RECT tr = { S(20), (int)(h * 0.12), w - S(20), (int)(h * 0.12) + S(56) };
    if (vizTitle[0]) text(dc, vizTitle, &tr, RGB(226, 238, 248), fBig, DT_CENTER | DT_END_ELLIPSIS);
    RECT sr = { S(20), tr.bottom, w - S(20), tr.bottom + S(24) }; text(dc, L"♪  Lecture audio", &sr, RGB(110, 150, 190), fUI, DT_CENTER);
}
/* rendu GDI+ : anti-crénelage, dégradés, halos — palette bleue */
static int draw_viz_gp(HDC dc, int w, int h) {
    double t = GetTickCount() / 1000.0;
    float bands[VB], lv = vizLvl, bass = 0, mid = 0, hi = 0;
    for (int k = 0; k < VB; k++) bands[k] = vizFallback ? (float)(0.25 + 0.2 * sin(t * 2.0 + k * 0.4)) : vizBands[k];
    if (vizFallback) lv = (float)(0.35 + 0.15 * sin(t * 1.3));
    for (int k = 0; k < 8; k++) bass += bands[k] / 8; for (int k = 8; k < 26; k++) mid += bands[k] / 18; for (int k = 26; k < VB; k++) hi += bands[k] / (VB - 26);
    void *g = NULL; if (pGpFromHDC(dc, &g) || !g) return 0;
    pGpSmooth(g, 4); pGpPixOff(g, 2);
    /* fond : dégradé marine profond -> bleu nuit */
    { GpRcF rc = { 0, 0, (float)w, (float)h }; void *lb = NULL;
      if (!pGpLinBr(&rc, GPA(255, 3, 9, 22), GPA(255, 8, 36, 76), 1, 0, &lb)) { pGpFillRect(g, lb, 0, 0, (float)w, (float)h); pGpDelBr(lb); } }
    gp_glow(g, VB_ACC, (int)(55 + 70 * lv), w * 0.55f, h * 0.66f, w * 0.75f, h * 0.60f);
    gp_glow(g, RGB(40, 110, 220), 38, w * 0.88f, h * 0.18f, w * 0.40f, h * 0.45f);
    int step = (w + 259) / 260; if (step < 3) step = 3;
    static GpPtF pa[900], pb[450]; static double cyv[450], tpv[450]; static int xs[450];
    /* grandes vagues douces d'arrière-plan */
    for (int j = 0; j < 2; j++) {
        int n = 0;
        for (int x = 0; x <= w + step; x += step) {
            double u = (double)(x > w ? w : x) / (w ? w : 1);
            double y = h * (0.50 - 0.30 * u * u * (3 - 2 * u) - 0.10 * j) + sin(u * 3.0 + t * 0.15 + j) * h * 0.02;
            pa[n].X = (float)x; pa[n].Y = (float)y; if (++n >= 440) break;
        }
        pa[n].X = (float)w; pa[n].Y = 0; pa[n + 1].X = 0; pa[n + 1].Y = 0;
        void *b = NULL; if (!pGpSolid(j ? GPA(46, 16, 70, 140) : GPA(38, 10, 50, 110), &b)) { pGpFillPoly(g, b, pa, n + 2, 0); pGpDelBr(b); }
    }
    /* lignes de contour fines (style fond d'écran Linux) */
    for (int j = -7; j <= 7; j++) {
        int n = 0;
        for (int x = 0; x <= w + step; x += step) {
            double u = (double)(x > w ? w : x) / (w ? w : 1);
            pa[n].X = (float)x; pa[n].Y = (float)(rib_cy(h, u, t * 0.3, 0, 0) + j * h * 0.050 + sin(u * 4.0 + j * 0.6 + t * 0.25) * h * 0.012); if (++n >= 440) break;
        }
        int al = 10 + (7 - abs(j)) * 2 + (int)(10 * lv); gp_pen_line(g, GPA(al, 90, 170, 240), (float)(S(1) > 1 ? S(1) * 0.8 : 1.0), pa, n);
    }
    /* étoiles / particules fixes qui scintillent */
    for (int i = 0; i < 44; i++) {
        double fx = fmod(i * 0.6180339887 + 0.13, 1.0), fy = fmod(i * 0.7548776662 + 0.31, 1.0);
        int al = (int)(60 + 60 * sin(t * (0.8 + (i % 5) * 0.3) + i)); if (al < 8) al = 8;
        gp_fill_ell(g, GPA(al, 170, 220, 255), (float)(fx * w), (float)(fy * h * 0.66), (float)(S(1) * (1 + (i % 3) * 0.5)), (float)(S(1) * (1 + (i % 3) * 0.5)));
    }
    /* bulles : mise à jour */
    { DWORD now = GetTickCount(); float dt = bubT ? (now - bubT) / 1000.0f : 0.03f; bubT = now; if (dt > 0.1f) dt = 0.1f;
      int spawn = 0; if (bass - prevBass > 0.08f && bass > 0.3f) spawn += 3 + (int)(bass * 4); prevBass = bass;
      if (rndf() < (0.10f + 0.9f * lv) * dt * 30.0f) spawn++;
      for (int s = 0; s < spawn; s++) for (int i = 0; i < 56; i++) if (!bub[i].on) {
          Bub *b = &bub[i]; double u = rndf(); b->x = (float)(u * w);
          b->y = (float)(rib_cy(h, u, t, 0, bass) + (rndf() - 0.5f) * S(30)); b->r = S(3) + rndf() * S(13) * (0.6f + bass);
          b->vy = -(S(16) + rndf() * S(46)) * (0.7f + lv); b->vx = (rndf() - 0.5f) * S(18); b->ph = rndf() * 6.28f; b->a = 1; b->on = 1; b->fillc = (rndf() < 0.3f && b->r < S(8)); break; }
      for (int i = 0; i < 56; i++) if (bub[i].on) {
          Bub *b = &bub[i]; b->y += b->vy * dt; b->x += b->vx * dt + (float)sin(b->ph + t) * S(6) * dt; b->a -= dt * 0.16f;
          if (b->a <= 0 || b->y < -b->r) b->on = 0; } }
    /* ruban lumineux */
    { int n = 0;
      for (int x = 0; x <= w + step; x += step) {
          double u = (double)(x > w ? w : x) / (w ? w : 1); double bi = u * (VB - 1); int b0 = (int)bi, b1 = b0 + 1 < VB ? b0 + 1 : b0; double fr = bi - b0;
          double m = bands[b0] * (1 - fr) + bands[b1] * fr;
          cyv[n] = rib_cy(h, u, t, m, bass); tpv[n] = pow(sin(3.14159265 * u), 0.7) * (1 + 0.6 * lv); xs[n] = x; if (++n >= 440) break; }
      for (int gI = 5; gI >= 0; gI--) {
          double wd = S(10) + S(10) * gI * (1 + lv); int k = 0;
          for (int i = 0; i < n; i++) { pa[k].X = (float)xs[i]; pa[k].Y = (float)(cyv[i] - wd * tpv[i] * 0.5); k++; }
          for (int i = n - 1; i >= 0; i--) { pa[k].X = (float)xs[i]; pa[k].Y = (float)(cyv[i] + wd * tpv[i] * 0.5); k++; }
          int al = (int)(10 + 6 * (5 - gI) + (gI < 2 ? 22 * lv : 0)); void *b = NULL;
          if (!pGpSolid(GPA(al, GetRValue(VB_ACC), GetGValue(VB_ACC), GetBValue(VB_ACC)), &b)) { pGpFillPoly(g, b, pa, k, 0); pGpDelBr(b); }
      }
      /* lueur autour de la ligne centrale */
      { int k = 0; for (int i = 0; i < n; i++) { pb[k].X = (float)xs[i]; pb[k].Y = (float)(cyv[i] + sin(xs[i] * 0.011 + t * 1.0) * S(2) * (1 + 3 * mid) * tpv[i]); k++; }
        gp_pen_line(g, GPA(26, 40, 160, 230), (float)S(14), pb, k); gp_pen_line(g, GPA(46, 60, 175, 240), (float)S(7), pb, k); }
      for (int l = 0; l < 9; l++) {
          double o = (l - 4) * S(3.4) * (1 + 0.8 * lv), ph = l * 0.8; int k = 0, cen = (l == 4);
          for (int i = 0; i < n; i++) { pb[k].X = (float)xs[i]; pb[k].Y = (float)(cyv[i] + o * tpv[i] + sin(xs[i] * 0.011 + t * (0.7 + 0.13 * l) + ph) * S(2) * (1 + 3 * mid) * tpv[i]); k++; }
          int al = cen ? 255 : (int)(70 + 22 * (4 - abs(l - 4)) + 60 * hi); if (al > 235) al = 235;
          COLORREF c = cen ? VB_CORE : VB_LIGHT; gp_pen_line(g, GPA(al, GetRValue(c), GetGValue(c), GetBValue(c)), cen ? (float)(S(2) + 0.4) : (float)(S(1) > 1 ? S(1) : 1.1), pb, k);
      } }
    /* cercle orange central : presque rond, tourne, pulse legerement avec la musique */
    { const int NP = 200; static GpPtF cp[210]; float cx = w * 0.5f, cy = h * 0.50f, R0 = (float)((w < h ? w : h) * 0.17);
      static double rot; static DWORD rt; DWORD nowr = GetTickCount(); double dtr = rt ? (nowr - rt) / 1000.0 : 0.03; rt = nowr; if (dtr > 0.1) dtr = 0.1;
      rot += dtr * (0.45 + 1.6 * lv + 1.2 * bass);                             /* vitesse liee au volume */
      R0 *= (float)(1.0 + 0.06 * bass + 0.03 * lv);
      /* anneau principal : legere ondulation qui voyage autour du cercle */
      for (int i = 0; i < NP; i++) { double th = 6.283185307 * i / NP;
          float r = (float)(R0 * (1.0 + 0.012 * sin(th * 5 - rot * 2.0) + (0.014 + 0.05 * mid) * sin(th * 3 + rot * 1.3)));
          cp[i].X = cx + (float)cos(th) * r; cp[i].Y = cy + (float)sin(th) * r; }
      cp[NP] = cp[0];
      { void *b = NULL; if (!pGpSolid(GPA((int)(30 + 36 * lv), 255, 120, 20), &b)) { pGpFillPoly(g, b, cp, NP, 0); pGpDelBr(b); } }
      gp_pen_line(g, GPA(40, 255, 110, 20), (float)S(16), cp, NP + 1); gp_pen_line(g, GPA(72, 255, 140, 30), (float)S(7), cp, NP + 1);
      gp_pen_line(g, GPA(255, 255, 190, 90), (float)S(2.6), cp, NP + 1);
      /* anneau interieur fin */
      for (int i = 0; i < NP; i++) { double th = 6.283185307 * i / NP; float r = R0 * 0.86f; cp[i].X = cx + (float)cos(th) * r; cp[i].Y = cy + (float)sin(th) * r; }
      cp[NP] = cp[0]; gp_pen_line(g, GPA(110, 255, 150, 50), (float)S(1.1), cp, NP + 1);
      /* 3 arcs lumineux qui tournent */
      for (int a = 0; a < 3; a++) { int k = 0; double a0 = rot * 1.15 + a * 2.0943951;
          for (int i = 0; i <= 40; i++) { double th = a0 + (0.95 * i / 40.0); float r = R0 * 1.10f; cp[k].X = cx + (float)cos(th) * r; cp[k].Y = cy + (float)sin(th) * r; k++; }
          gp_pen_line(g, GPA(60, 255, 120, 20), (float)S(9), cp, k); gp_pen_line(g, GPA(230, 255, 215, 140), (float)S(2.4), cp, k); }
      /* graduations exterieures qui tournent en sens inverse, longueur selon le spectre */
      for (int i = 0; i < 60; i++) { double th = -rot * 0.55 + 6.283185307 * i / 60; int bi = (i < 30 ? i : 59 - i) * (VB - 1) / 29; double m = bands[bi];
          float r1 = R0 * 1.22f, r2 = r1 + (float)(S(4) + S(16) * m); GpPtF tk[2] = { { cx + (float)cos(th) * r1, cy + (float)sin(th) * r1 }, { cx + (float)cos(th) * r2, cy + (float)sin(th) * r2 } };
          gp_pen_line(g, GPA((int)(80 + 150 * m), 255, 160, 50), (float)(S(1.6) > 1.4 ? S(1.6) : 1.4), tk, 2); }
      gp_glow(g, RGB(255, 130, 25), (int)(40 + 70 * bass), cx, cy, R0 * 1.9f, R0 * 1.9f);
      gp_fill_ell(g, GPA((int)(90 + 120 * bass), 255, 225, 160), cx, cy, (float)(R0 * (0.08 + 0.10 * bass)), (float)(R0 * (0.08 + 0.10 * bass))); }
    /* bulles : halo radial + anneau net + reflet */
    for (int i = 0; i < 56; i++) if (bub[i].on) {
        Bub *b = &bub[i]; double a = b->a * (0.40 + 0.60 * (lv * 1.6 > 1 ? 1 : lv * 1.6 + 0.15));
        double r = b->r * (1 + 0.25 * bass * sin(t * 6 + b->ph)); if (r < 2) r = 2;
        gp_glow(g, VB_ACC, (int)(a * 110), b->x, b->y, (float)(r * 2.8), (float)(r * 2.8));
        if (b->fillc) { gp_fill_ell(g, GPA((int)(a * 230), 90, 190, 255), b->x, b->y, (float)(r * 0.55), (float)(r * 0.55)); continue; }
        gp_ring(g, GPA((int)(a * 70), 40, 150, 230), (float)S(4), b->x, b->y, (float)r);
        gp_ring(g, GPA((int)(a * 235), 150, 220, 255), (float)(r > S(8) ? S(1.6) : S(1.1)), b->x, b->y, (float)r);
        gp_fill_ell(g, GPA((int)(a * 190), 235, 248, 255), (float)(b->x - r * 0.38), (float)(b->y - r * 0.38), (float)(r * 0.16 + 0.6), (float)(r * 0.16 + 0.6));
    }
    pGpDelG(g);
    viz_title(dc, w, h);
    return 1;
}
static void draw_viz(HDC dc, int w, int h) { if (gp_init() && draw_viz_gp(dc, w, h)) return; draw_viz_gdi(dc, w, h); }

static LRESULT CALLBACK VizProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT rc; GetClientRect(h, &rc);
        HDC md = CreateCompatibleDC(dc); HBITMAP bm = CreateCompatibleBitmap(dc, rc.right, rc.bottom); HGDIOBJ old = SelectObject(md, bm);
        draw_viz(md, rc.right, rc.bottom); BitBlt(dc, 0, 0, rc.right, rc.bottom, md, 0, 0, SRCCOPY);
        SelectObject(md, old); DeleteObject(bm); DeleteDC(md); EndPaint(h, &ps); return 0; }
    case WM_TIMER: if (wp == 3) InvalidateRect(h, NULL, FALSE); return 0;
    case WM_LBUTTONDOWN: SetFocus(hMain); return 0;
    case WM_LBUTTONDBLCLK: PostMessage(hMain, WM_LAV_FS, 0, 0); return 0;
    case WM_DROPFILES: SendMessage(hMain, m, wp, lp); return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

/* ---------- fenêtre panneau ---------- */
static LRESULT CALLBACK PanelProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_ERASEBKGND: return 1;
    case WM_MOUSEACTIVATE: return MA_NOACTIVATE;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT rc; GetClientRect(h, &rc);
        HDC md = CreateCompatibleDC(dc); HBITMAP bm = CreateCompatibleBitmap(dc, rc.right, rc.bottom);
        HGDIOBJ old = SelectObject(md, bm);
        paint_panel(md, rc.right, rc.bottom);
        BitBlt(dc, 0, 0, rc.right, rc.bottom, md, 0, 0, SRCCOPY);
        SelectObject(md, old); DeleteObject(bm); DeleteDC(md); EndPaint(h, &ps); return 0; }
    case WM_MOUSEMOVE: {
        int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp);
        if (dragSeek) { set_seek_x(x); InvalidateRect(h, NULL, FALSE); }
        else if (dragVol) { set_vol_x(x); InvalidateRect(h, NULL, FALSE); }
        else { int nh = hit(x, y); if (nh == H_SEEK || nh == H_VOL) nh = 0;
               if (nh != hover) { hover = nh; InvalidateRect(h, NULL, FALSE); }
               TRACKMOUSEEVENT t = { sizeof t, TME_LEAVE, h, 0 }; TrackMouseEvent(&t); }
        return 0; }
    case WM_MOUSELEAVE: hover = 0; InvalidateRect(h, NULL, FALSE); return 0;
    case WM_LBUTTONDOWN: {
        int x = GET_X_LPARAM(lp), y = GET_Y_LPARAM(lp), t = hit(x, y);
        SetFocus(hMain);
        switch (t) {
        case H_SEEK: if (gDur > 0) { dragSeek = 1; SetCapture(h); set_seek_x(x); InvalidateRect(h, NULL, FALSE); } break;
        case H_VOL: dragVol = 1; SetCapture(h); set_vol_x(x); InvalidateRect(h, NULL, FALSE); break;
        case H_OPEN: open_dialog(); break;
        case H_PLAY: toggle_pause(); break;
        case H_STOP: cmd("stop", NULL, NULL, NULL); playing = 0; viz_update(1); gPos = gDur = -1; nAud = nSub = 0; InvalidateRect(hVideo, NULL, TRUE); InvalidateRect(h, NULL, FALSE); break;
        case H_FS: toggle_fs(); break;
        case H_TOG: toggle_tracks(); break;
        case H_AUD: pick_menu(1); break;
        case H_SUB: pick_menu(0); break;
        case H_GEAR: settings_window(); break;
        case H_CAM: capture_open(); break;
        case H_IPTV: iptv_menu(); break;
        case H_IPTVCFG: manage_window(); break;
        case H_LANG: lang_menu(); break;
        case H_CAT: cat_menu(); break;
        case H_CHAN: chan_menu(); break;
        }
        return 0; }
    case WM_LBUTTONUP:
        if (dragSeek) {
            ReleaseCapture(); dragSeek = 0; char v[32]; snprintf(v, sizeof v, "%.3f", seekFrac * 100);
            cmd("seek", v, "absolute-percent", NULL); gPos = seekFrac * gDur;
        }
        if (dragVol) { ReleaseCapture(); dragVol = 0; }
        InvalidateRect(h, NULL, FALSE); return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}


/* ---------- fenêtre vidéo (hôte de mpv) ---------- */
static LRESULT CALLBACK VideoProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_ERASEBKGND: { RECT r; GetClientRect(h, &r); fill((HDC)wp, &r, RGB(0, 0, 0)); return 1; }
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT r; GetClientRect(h, &r);
        fill(dc, &r, RGB(0, 0, 0));
        if (!playing) text(dc, L"Ouvrir un fichier (O) ou glisser-déposer", &r, C_DIM, fUI, DT_CENTER);
        EndPaint(h, &ps); return 0; }
    case WM_DROPFILES: SendMessage(hMain, m, wp, lp); return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

/* ---------- fenêtre principale ---------- */
static void make_fonts(void) {
    if (fUI) { DeleteObject(fUI); DeleteObject(fMono); DeleteObject(fSmall); }
    fUI = CreateFontW(-MulDiv(9, dpi, 72), 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    fSmall = CreateFontW(-MulDiv(8, dpi, 72), 0, 0, 0, FW_SEMIBOLD, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
    fMono = CreateFontW(-MulDiv(9, dpi, 72), 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Consolas");
}

static void key(WPARAM k) {
    switch (k) {
    case VK_SPACE: toggle_pause(); break;
    case 'F': toggle_fs(); break;
    case VK_ESCAPE: if (fullscreen) toggle_fs(); break;
    case 'T': toggle_tracks(); break;
    case 'O': open_dialog(); break;
    case 'M': cmd("cycle", "mute", NULL, NULL); break;
    case VK_LEFT: cmd("seek", "-5", NULL, NULL); break;
    case VK_RIGHT: cmd("seek", "5", NULL, NULL); break;
    case VK_UP: cmd("add", "volume", "5", NULL); break;
    case VK_DOWN: cmd("add", "volume", "-5", NULL); break;
    }
}

static void poll(void) {
    double d;
    if (p_get_property(mpv, "time-pos", MPV_FMT_DOUBLE, &d) == 0) gPos = d; else if (!playing) gPos = -1;
    if (p_get_property(mpv, "duration", MPV_FMT_DOUBLE, &d) == 0) gDur = d; else if (!playing) gDur = -1;
    if (p_get_property(mpv, "volume", MPV_FMT_DOUBLE, &d) == 0 && !dragVol) gVol = d;
    int f;
    if (p_get_property(mpv, "pause", MPV_FMT_FLAG, &f) == 0) gPause = f;
    if (p_get_property(mpv, "mute", MPV_FMT_FLAG, &f) == 0) gMute = f;
    if (playing) {
        char *c = p_get_property_string(mpv, "track-list/count"); int n = c ? atoi(c) : 0; if (c) p_free(c);
        if (n != lastCount) refresh_tracks();
    }
    inval();
    POINT p; GetCursorPos(&p);
    if (abs(p.x - lastPt.x) + abs(p.y - lastPt.y) > 6) { lastPt = p; lastMove = GetTickCount(); }
    if (fullscreen && !menuOpen && !dragSeek && !dragVol) {
        HWND fg = GetForegroundWindow();
        int active = fg && (fg == hMain || GetAncestor(fg, GA_ROOTOWNER) == hMain);
        int show = active && lastMove && (GetTickCount() - lastMove < 2500);   /* uniquement si la souris a bougé */
        if (show != barsShown) { barsShown = show; do_layout(); }
    }
}

static LRESULT CALLBACK MainProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_SIZE: if (hPanelFs) do_layout(); return 0;
    case WM_MOVE: if (hPanelFs && fullscreen) do_layout(); return 0;
    case WM_GETMINMAXINFO: ((MINMAXINFO *)lp)->ptMinTrackSize.x = S(980); ((MINMAXINFO *)lp)->ptMinTrackSize.y = S(380); return 0;
    case WM_ERASEBKGND: return 1;
    case WM_KEYDOWN: key(wp); return 0;
    case WM_TIMER: poll(); return 0;
    case WM_LAV_LOADED: {
        playing = 1; refresh_tracks(); InvalidateRect(hVideo, NULL, TRUE);
        if (chanTitle[0]) { wchar_t o[600]; _snwprintf(o, 599, L"%s \u2014 IPTV \u2014 Lecteur A/V", chanTitle); o[599] = 0; SetWindowTextW(h, o); return 0; }
        char *t = p_get_property_string(mpv, "media-title");
        if (t) { wchar_t w[512], o[600]; u8w(t, w, 512); _snwprintf(o, 599, L"%s — Lecteur A/V", w); o[599] = 0; SetWindowTextW(h, o); p_free(t); }
        return 0; }
    case WM_LAV_FS: toggle_fs(); return 0;
    case WM_LAV_ESC: if (fullscreen) toggle_fs(); return 0;
    case WM_LAV_TRACKS: toggle_tracks(); return 0;
    case WM_LAV_OPEN: open_dialog(); return 0;
    case WM_LAV_NEWVER: {
        wchar_t t[200]; _snwprintf(t, 199, L"Une nouvelle version du lecteur est disponible : %s  (actuelle : %s).\n\nL'installer maintenant ?\nVos listes et votre configuration sont conservées.", gNewVer, LAV_VERSION); t[199] = 0;
        if (MessageBoxW(h, t, L"Mise à jour", MB_YESNO | MB_ICONQUESTION) == IDYES) { if (app_install_online(h)) PostMessage(h, WM_CLOSE, 0, 0); }
        else { wchar_t ip[MAX_PATH]; app_ini(ip); WritePrivateProfileStringW(L"capture", L"maj_refus", gNewVer, ip); }
        return 0; }
    case WM_DROPFILES: { wchar_t f[2048]; if (DragQueryFileW((HDROP)wp, 0, f, 2048)) load_file(f); DragFinish((HDROP)wp); return 0; }
    case WM_DPICHANGED: {
        dpi = HIWORD(wp); make_fonts(); RECT *r = (RECT *)lp;
        SetWindowPos(h, NULL, r->left, r->top, r->right - r->left, r->bottom - r->top, SWP_NOZORDER | SWP_NOACTIVATE);
        do_layout(); return 0; }
    case WM_CLOSE: vizStop = 1; cap_shutdown(); if (hCap) DestroyWindow(hCap); DestroyWindow(h); return 0;
    case WM_DESTROY: PostQuitMessage(0); return 0;
    }
    return DefWindowProc(h, m, wp, lp);
}

static DWORD WINAPI ev_thread(LPVOID p) {
    (void)p;
    for (;;) {
        mpv_event *e = p_wait_event(mpv, -1);
        if (e->event_id == EV_SHUTDOWN) break;
        if (e->event_id == EV_FILE_LOADED) PostMessage(hMain, WM_LAV_LOADED, 0, 0);
        else if (e->event_id == EV_CLIENT_MSG && e->data) {
            mpv_event_client_message *c = (mpv_event_client_message *)e->data;
            if (c->num_args >= 1) {
                const char *a = c->args[0];
                if (!strcmp(a, "lav-fs")) PostMessage(hMain, WM_LAV_FS, 0, 0);
                else if (!strcmp(a, "lav-esc")) PostMessage(hMain, WM_LAV_ESC, 0, 0);
                else if (!strcmp(a, "lav-tracks")) PostMessage(hMain, WM_LAV_TRACKS, 0, 0);
                else if (!strcmp(a, "lav-open")) PostMessage(hMain, WM_LAV_OPEN, 0, 0);
            }
        }
    }
    return 0;
}

static HMODULE load_mpv(void) {
    wchar_t dir[MAX_PATH], p[MAX_PATH]; GetModuleFileNameW(NULL, dir, MAX_PATH);
    wchar_t *s = wcsrchr(dir, L'\\'); if (s) *s = 0;
    const wchar_t *names[] = { L"codec\\libmpv-2.dll", L"codec\\mpv-2.dll", L"libmpv-2.dll", L"mpv-2.dll", L"lib\\libmpv-2.dll", L"lib\\mpv-2.dll", L"ffmpeg\\libmpv-2.dll", L"ffmpeg\\mpv-2.dll" };
    SetDllDirectoryW(dir);
    for (int i = 0; i < 8; i++) {
        _snwprintf(p, MAX_PATH - 1, L"%s\\%s", dir, names[i]); p[MAX_PATH - 1] = 0;
        HMODULE m = LoadLibraryExW(p, NULL, LOAD_WITH_ALTERED_SEARCH_PATH); if (m) return m;
    }
    return NULL;
}

#define LOAD(n) do { *(void **)&p_##n = (void *)GetProcAddress(dll, "mpv_" #n); if (!p_##n) return 0; } while (0)
static int bind_mpv(HMODULE dll) {
    LOAD(create); LOAD(initialize); LOAD(set_option_string); LOAD(command); LOAD(get_property);
    LOAD(get_property_string); LOAD(set_property_string); LOAD(wait_event); LOAD(free); LOAD(terminate_destroy);
    return 1;
}

int WINAPI wWinMain(HINSTANCE hi, HINSTANCE hp, LPWSTR cl, int sw) {
    (void)hp; (void)cl; hInst = hi;
    /* thème sombre (menus contextuels, barre de titre) */
    HMODULE ux = LoadLibraryW(L"uxtheme.dll");
    if (ux) { int (WINAPI *f)(int) = (void *)GetProcAddress(ux, MAKEINTRESOURCEA(135)); if (f) f(2);
              void (WINAPI *g)(void) = (void *)GetProcAddress(ux, MAKEINTRESOURCEA(136)); if (g) g(); }

    CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);
    HMODULE dll = load_mpv();
    if (dll) { gDll = dll; GetModuleFileNameW(dll, gDllPath, MAX_PATH); wchar_t od[MAX_PATH]; _snwprintf(od, MAX_PATH - 1, L"%s.old", gDllPath); od[MAX_PATH - 1] = 0; DeleteFileW(od); }
    if (!dll) { install_window(1, !ff_present(), 1); return 0; }      /* telecharge et installe libmpv puis relance le lecteur */
    if (!bind_mpv(dll)) {
        MessageBoxW(NULL, L"libmpv-2.dll est invalide ou incompatible (x64 requis).\n\nSupprimez ce fichier : le lecteur proposera de le r\u00e9installer au prochain lancement.", L"Lecteur A/V", MB_ICONERROR);
        return 1;
    }

    { wchar_t o[MAX_PATH]; ff_path(o); wcscat(o, L".old"); DeleteFileW(o); }
    { wchar_t o[MAX_PATH]; GetModuleFileNameW(NULL, o, MAX_PATH); wcscat(o, L".old"); DeleteFileW(o); }
    if (!ff_present() && !ini_i(L"ff_refuse", 0)) {            /* bibliotheque de capture absente du dossier codec */
        int r = install_window(0, 1, 1); if (r == -1) ini_si(L"ff_refuse", 1); else if (r == 1) ini_si(L"ff_refuse", 0);
    }
    WNDCLASSW wc; memset(&wc, 0, sizeof wc);
    wc.hInstance = hi; wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hIcon = LoadIconW(hi, MAKEINTRESOURCEW(1));
    wc.lpfnWndProc = MainProc; wc.lpszClassName = L"LavMain"; wc.hbrBackground = CreateSolidBrush(RGB(0, 0, 0)); RegisterClassW(&wc);
    wc.hIcon = NULL; wc.lpfnWndProc = PanelProc; wc.lpszClassName = L"LavPanel"; wc.hbrBackground = NULL; RegisterClassW(&wc);
    wc.lpfnWndProc = VideoProc; wc.lpszClassName = L"LavVideo"; RegisterClassW(&wc);
    wc.style = CS_DBLCLKS; wc.lpfnWndProc = VizProc; wc.lpszClassName = L"LavViz"; RegisterClassW(&wc); wc.style = 0;

    { INITCOMMONCONTROLSEX icc = { sizeof icc, ICC_LISTVIEW_CLASSES }; InitCommonControlsEx(&icc); }
    iptv_init_dir(); load_sel();
    hMain = CreateWindowExW(WS_EX_ACCEPTFILES, L"LavMain", L"Lecteur A/V", WS_OVERLAPPEDWINDOW | WS_CLIPCHILDREN,
                            CW_USEDEFAULT, CW_USEDEFAULT, 1100, 700, NULL, NULL, hi, NULL);
    typedef UINT (WINAPI *PGD)(HWND);
    PGD gd = (PGD)GetProcAddress(GetModuleHandleW(L"user32.dll"), "GetDpiForWindow");
    if (gd) dpi = gd(hMain);
    make_fonts();
    SendMessage(hMain, WM_SETICON, ICON_BIG, (LPARAM)LoadImageW(hi, MAKEINTRESOURCEW(1), IMAGE_ICON, GetSystemMetrics(SM_CXICON), GetSystemMetrics(SM_CYICON), 0));
    SendMessage(hMain, WM_SETICON, ICON_SMALL, (LPARAM)LoadImageW(hi, MAKEINTRESOURCEW(1), IMAGE_ICON, GetSystemMetrics(SM_CXSMICON), GetSystemMetrics(SM_CYSMICON), 0));
    BOOL dark = TRUE; HMODULE dwm = LoadLibraryW(L"dwmapi.dll");
    if (dwm) { HRESULT (WINAPI *f)(HWND, DWORD, LPCVOID, DWORD) = (void *)GetProcAddress(dwm, "DwmSetWindowAttribute");
               if (f) { f(hMain, 20, &dark, sizeof dark); f(hMain, 19, &dark, sizeof dark); } }
    SetWindowPos(hMain, NULL, 0, 0, S(1100), S(700), SWP_NOMOVE | SWP_NOZORDER);

    hVideo = CreateWindowExW(WS_EX_ACCEPTFILES, L"LavVideo", NULL, WS_CHILD | WS_VISIBLE | WS_CLIPCHILDREN | WS_CLIPSIBLINGS, 0, 0, 10, 10, hMain, NULL, hi, NULL);
    hViz = CreateWindowExW(WS_EX_ACCEPTFILES, L"LavViz", NULL, WS_CHILD | WS_CLIPSIBLINGS, 0, 0, 10, 10, hMain, NULL, hi, NULL);
    hPanel = CreateWindowExW(0, L"LavPanel", NULL, WS_CHILD | WS_VISIBLE | WS_CLIPSIBLINGS, 0, 0, 10, 10, hMain, NULL, hi, NULL);

    hPanelFs = CreateWindowExW(WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE, L"LavPanel", NULL, WS_POPUP,
                               0, 0, 10, 10, hMain, NULL, hi, NULL);

    mpv = p_create();
    char wid[32]; snprintf(wid, sizeof wid, "%lld", (long long)(intptr_t)hVideo);
    p_set_option_string(mpv, "wid", wid);
    p_set_option_string(mpv, "idle", "yes");
    p_set_option_string(mpv, "vo", "gpu");
    p_set_option_string(mpv, "profile", "gpu-hq");      /* meilleure qualité de mise à l'échelle */
    p_set_option_string(mpv, "hwdec", "auto-safe");
    p_set_option_string(mpv, "keepaspect", "yes");      /* aucune déformation de l'image */
    p_set_option_string(mpv, "keep-open", "yes");
    p_set_option_string(mpv, "osc", "no");
    p_set_option_string(mpv, "osd-level", "1");
    p_set_option_string(mpv, "input-default-bindings", "yes");
    p_set_option_string(mpv, "input-vo-keyboard", "yes");
    p_set_option_string(mpv, "audio-channels", "auto-safe");
    p_set_option_string(mpv, "sub-auto", "fuzzy");
    p_set_option_string(mpv, "volume-max", "130");
    p_set_option_string(mpv, "cursor-autohide", "1500");
    p_set_option_string(mpv, "network-timeout", "15");
    p_set_option_string(mpv, "user-agent", "VLC/3.0.20 LibVLC/3.0.20");
    p_set_option_string(mpv, "screenshot-directory", "~~desktop/");
    if (p_initialize(mpv) < 0) { MessageBoxW(NULL, L"Initialisation de libmpv impossible.", L"Lecteur A/V", MB_ICONERROR); return 1; }
    cmd("keybind", "f", "script-message lav-fs", NULL);
    cmd("keybind", "MBTN_LEFT_DBL", "script-message lav-fs", NULL);
    cmd("keybind", "ESC", "script-message lav-esc", NULL);
    cmd("keybind", "t", "script-message lav-tracks", NULL);
    cmd("keybind", "o", "script-message lav-open", NULL);
    cmd("keybind", "q", "ignore", NULL); cmd("keybind", "Q", "ignore", NULL);
    hThread = CreateThread(NULL, 0, ev_thread, NULL, 0, NULL);

    ShowWindow(hMain, sw); do_layout();
    SetTimer(hMain, 1, 200, NULL);
    SetFocus(hMain);

    int argc; wchar_t **argv = CommandLineToArgvW(GetCommandLineW(), &argc);
    if (argv && argc > 1) load_file(argv[1]);
    CloseHandle(CreateThread(NULL, 0, app_check_thread, NULL, 0, NULL));   /* nouvelle version sur GitHub ? */

    MSG msg;
    while (GetMessage(&msg, NULL, 0, 0) > 0) { TranslateMessage(&msg); DispatchMessage(&msg); }

    cmd("quit", NULL, NULL, NULL);
    if (hThread) WaitForSingleObject(hThread, 3000);
    p_terminate_destroy(mpv);
    return 0;
}
