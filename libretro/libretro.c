#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>

#ifdef _MSC_VER
#include <compat/msvc.h>
#endif

#include <libretro.h>
#include <string/stdstring.h>
#include <file/file_path.h>
#include <streams/file_stream.h>
#include <streams/memory_stream.h>
#include <libretro_dipswitch.h>
#include <libretro_core_options.h>

#include "../src/fceu.h"
#include "../src/fceu-endian.h"
#include "../src/input.h"
#include "../src/state.h"
#include "../src/ppu.h"
#include "../src/cart.h"
#include "../src/x6502.h"
#include "../src/git.h"
#include "../src/palette.h"
#include "../src/sound.h"
#include "../src/file.h"
#include "../src/cheat.h"
#include "../src/ines.h"
#include "../src/unif.h"
#include "../src/fds.h"
#include "../src/vsuni.h"
#include "../src/video.h"
#include "../src/gamegenie.h"

#include "libretro_input.h"
#include "paldef.h"

#if defined(PSP)
#include "pspgu.h"
#endif

#if defined(PS2)
#include "libretro-common/include/libretro_gskit_ps2.h"
#endif

#if defined(PSP)
#define RED_SHIFT    0
#define GREEN_SHIFT  5
#define BLUE_SHIFT   11
#define RED_EXPAND   3
#define GREEN_EXPAND 2
#define BLUE_EXPAND  3
#define BUILD_PIXEL(R, G, B) (((int)((R)&0x1f) << RED_SHIFT) | ((int)((G)&0x3f) << GREEN_SHIFT) | ((int)((B)&0x1f) << BLUE_SHIFT))
typedef uint16 Bpp_t;
#elif defined(FRONTEND_SUPPORTS_ABGR1555) /* PS2 */
typedef uint16 Bpp_t;
#define RED_SHIFT    0
#define GREEN_SHIFT  5
#define BLUE_SHIFT   10
#define RED_EXPAND   3
#define GREEN_EXPAND 3
#define BLUE_EXPAND  3
#define RED_MASK     0x1F
#define GREEN_MASK   0x3E0
#define BLUE_MASK    0x7C00
#define BUILD_PIXEL(R, G, B) (((int)((R)&0x1f) << RED_SHIFT) | ((int)((G)&0x3f) << GREEN_SHIFT) | ((int)((B)&0x1f) << BLUE_SHIFT))
typedef uint16 Bpp_t;
#elif defined(FRONTEND_SUPPORTS_RGB565)
typedef uint16 Bpp_t;
#define RED_SHIFT    11
#define GREEN_SHIFT  5
#define BLUE_SHIFT   0
#define RED_EXPAND   3
#define GREEN_EXPAND 2
#define BLUE_EXPAND  3
#define RED_MASK     0xF800
#define GREEN_MASK   0x7e0
#define BLUE_MASK    0x1f
#define BUILD_PIXEL(R, G, B) (((int)((R)&0x1f) << RED_SHIFT) | ((int)((G)&0x3f) << GREEN_SHIFT) | ((int)((B)&0x1f) << BLUE_SHIFT))
#elif defined(FRONTEND_SUPPORTS_ARGB888)
typedef uint32 Bpp_t;
#define RED_SHIFT    16
#define GREEN_SHIFT  8
#define BLUE_SHIFT   0
#define RED_EXPAND   0
#define GREEN_EXPAND 0
#define BLUE_EXPAND  0
#define ALPHA_SHIFT 24
#define BUILD_PIXEL(R, G, B) (((int)(R) << RED_SHIFT) | ((int)(G) << GREEN_SHIFT) | ((int)(B) << BLUE_SHIFT))
#else
typedef uint16 Bpp_t;
#define RED_SHIFT    10
#define GREEN_SHIFT  5
#define BLUE_SHIFT   0
#define RED_EXPAND   3
#define GREEN_EXPAND 3
#define BLUE_EXPAND  3
#define BUILD_PIXEL(R, G, B) (((int)((R)&0x1f) << RED_SHIFT) | ((int)((G)&0x3f) << GREEN_SHIFT) | ((int)((B)&0x1f) << BLUE_SHIFT))
#endif

#define NES_8_7_PAR       ((NES_WIDTH - (overscan_left + overscan_right)) * (8.0 / 7.0)) / (NES_HEIGHT - (overscan_top + overscan_bottom))
#define NES_4_3           (((NES_WIDTH - (overscan_left + overscan_right)) / ((NES_HEIGHT - (overscan_top + overscan_bottom)) * (NES_WIDTH / NES_HEIGHT))) * 4.0 / 3.0)
#define NES_PP            (((NES_WIDTH - (overscan_left + overscan_right)) / ((NES_HEIGHT - (overscan_top + overscan_bottom)) * (NES_WIDTH / NES_HEIGHT))) * 16.0 / 15.0)
#define NES_TARGET_FPS    ((double)FCEUI_GetDesiredFPS() / 16777215.0)

#if defined(_3DS)
void *linearMemAlign(size_t size, size_t alignment);
void linearFree(void *mem);
#endif

#if defined(PS2)
RETRO_HW_RENDER_INTEFACE_GSKIT_PS2 *ps2 = NULL;
#endif

static retro_video_refresh_t video_cb            = NULL;
static retro_input_poll_t poll_cb                = NULL;
static retro_input_state_t input_cb              = NULL;
static retro_audio_sample_batch_t audio_batch_cb = NULL;
static retro_environment_t environ_cb            = NULL;
static struct retro_log_callback log_cb          = { 0 };

#if defined(PSP)
static bool crop_overscan;
#endif

static unsigned overscan_left    = 0;
static unsigned overscan_right   = 0;
static unsigned overscan_top     = 0;
static unsigned overscan_bottom  = 0;
static unsigned aspect_ratio_par = 0;

static bool use_raw_palette = false;

bool libretro_supports_bitmasks                 = false;
static bool libretro_supports_option_categories = false;
static unsigned libretro_msg_interface_version  = 0;

/* emulator-specific variables */

const size_t PPU_BIT = 1ULL << 31ULL;

static uint8 opt_region              = 0;
static bool opt_showAdvSoundOptions  = true;
static bool opt_showAdvSystemOptions = true;

#if defined(PSP) || defined(PS2)
static __attribute__((aligned(16))) uint16 retro_palette[1024];
#else
static Bpp_t retro_palette[1024];
#endif
#if defined(PSP) || defined(PS2)
/* not used because of hw buffers? */
/* static uint8* fceu_video_out; */
#else
static Bpp_t *fceu_video_out;
#endif

/* Some timing-related variables. */
static uint8 sndquality;

static uint32 current_palette = 0;
static unsigned serialize_size;

/* extern forward decls.*/
extern uint8 PALRAM[0x20];
extern uint8 SPRAM[0x100];

extern int palette_game_available;
extern int palette_user_available;

/* emulator-specific callback functions */
const char *GetKeyboard(void);
const char *GetKeyboard(void) {
	return "";
}

void FCEUD_SetPalette(int index, uint8 r, uint8 g, uint8 b) {
	unsigned index_to_write = index;
#if defined(PS2)
	/* Index correction for PS2 GS */
	int modi = index & 63;
	if ((modi >= 8 && modi < 16) || (modi >= 40 && modi < 48)) {
		index_to_write += 8;
	} else if ((modi >= 16 && modi < 24) || (modi >= 48 && modi < 56)) {
		index_to_write -= 8;
	}
#endif
    retro_palette[index_to_write] = BUILD_PIXEL(r >> RED_EXPAND, g >> GREEN_EXPAND, b >> BLUE_EXPAND);
}

static void default_logger(enum retro_log_level level, const char *fmt, ...) {
}

void FCEUD_PrintError(char *c) {
	log_cb.log(RETRO_LOG_WARN, "%s", c);
}

void FCEUD_PrintDebug(char *c) {
	log_cb.log(RETRO_LOG_DEBUG, "%s", c);
}

void FCEUD_Message(char *s) {
	log_cb.log(RETRO_LOG_INFO, "%s", s);
}

void FCEUD_DispMessage(enum retro_log_level level, unsigned duration, const char *str) {
	if (!environ_cb)
		return;

	if (libretro_msg_interface_version >= 1) {
		struct retro_message_ext msg;
		unsigned priority;

		switch (level) {
		case RETRO_LOG_ERROR:
			priority = 5;
			break;
		case RETRO_LOG_WARN:
			priority = 4;
			break;
		case RETRO_LOG_INFO:
			priority = 3;
			break;
		case RETRO_LOG_DEBUG:
		default:
			priority = 1;
			break;
		}

		msg.msg      = str;
		msg.duration = duration;
		msg.priority = priority;
		msg.level    = level;
		msg.target   = RETRO_MESSAGE_TARGET_OSD;
		msg.type     = RETRO_MESSAGE_TYPE_NOTIFICATION_ALT;
		msg.progress = -1;

		environ_cb(RETRO_ENVIRONMENT_SET_MESSAGE_EXT, &msg);
	} else {
		float fps       = NES_TARGET_FPS;
		unsigned frames = (unsigned)(((float)duration * fps / 1000.0f) + 0.5f);
		struct retro_message msg;

		msg.msg    = str;
		msg.frames = frames;

		environ_cb(RETRO_ENVIRONMENT_SET_MESSAGE, &msg);
	}
}

/*palette for FCEU*/
<<<<<<< HEAD
#define PAL_INTERNAL sizeof(palettes) / sizeof(palettes[0]) /* Number of palettes in palettes[] */
#define PAL_DEFAULT  (PAL_INTERNAL + 1)
#define PAL_RAW      (PAL_INTERNAL + 2)
#define PAL_CUSTOM   (PAL_INTERNAL + 3)
#define PAL_TOTAL    PAL_CUSTOM

static int external_palette_exist = 0;
extern int ipalette;

/* table for currently loaded palette */
static uint8_t base_palette[192];

struct st_palettes {
   char name[32];
   char desc[32];
   unsigned int data[64];
};

struct st_palettes palettes[] = {
   { "asqrealc", "AspiringSquire's Real palette",
      { 0x6c6c6c, 0x00268e, 0x0000a8, 0x400094,
         0x700070, 0x780040, 0x700000, 0x621600,
         0x442400, 0x343400, 0x005000, 0x004444,
         0x004060, 0x000000, 0x101010, 0x101010,
         0xbababa, 0x205cdc, 0x3838ff, 0x8020f0,
         0xc000c0, 0xd01474, 0xd02020, 0xac4014,
         0x7c5400, 0x586400, 0x008800, 0x007468,
         0x00749c, 0x202020, 0x101010, 0x101010,
         0xffffff, 0x4ca0ff, 0x8888ff, 0xc06cff,
         0xff50ff, 0xff64b8, 0xff7878, 0xff9638,
         0xdbab00, 0xa2ca20, 0x4adc4a, 0x2ccca4,
         0x1cc2ea, 0x585858, 0x101010, 0x101010,
         0xffffff, 0xb0d4ff, 0xc4c4ff, 0xe8b8ff,
         0xffb0ff, 0xffb8e8, 0xffc4c4, 0xffd4a8,
         0xffe890, 0xf0f4a4, 0xc0ffc0, 0xacf4f0,
         0xa0e8ff, 0xc2c2c2, 0x202020, 0x101010 }
   },
   { "nintendo-vc", "Virtual Console palette",
      { 0x494949, 0x00006a, 0x090063, 0x290059,
         0x42004a, 0x490000, 0x420000, 0x291100,
         0x182700, 0x003010, 0x003000, 0x002910,
         0x012043, 0x000000, 0x000000, 0x000000,
         0x747174, 0x003084, 0x3101ac, 0x4b0194,
         0x64007b, 0x6b0039, 0x6b2101, 0x5a2f00,
         0x424900, 0x185901, 0x105901, 0x015932,
         0x01495a, 0x101010, 0x000000, 0x000000,
         0xadadad, 0x4a71b6, 0x6458d5, 0x8450e6,
         0xa451ad, 0xad4984, 0xb5624a, 0x947132,
         0x7b722a, 0x5a8601, 0x388e31, 0x318e5a,
         0x398e8d, 0x383838, 0x000000, 0x000000,
         0xb6b6b6, 0x8c9db5, 0x8d8eae, 0x9c8ebc,
         0xa687bc, 0xad8d9d, 0xae968c, 0x9c8f7c,
         0x9c9e72, 0x94a67c, 0x84a77b, 0x7c9d84,
         0x73968d, 0xdedede, 0x000000, 0x000000 }
   },
   { "rgb", "Nintendo RGB PPU palette",
      { 0x6D6D6D, 0x002492, 0x0000DB, 0x6D49DB,
         0x92006D, 0xB6006D, 0xB62400, 0x924900,
         0x6D4900, 0x244900, 0x006D24, 0x009200,
         0x004949, 0x000000, 0x000000, 0x000000,
         0xB6B6B6, 0x006DDB, 0x0049FF, 0x9200FF,
         0xB600FF, 0xFF0092, 0xFF0000, 0xDB6D00,
         0x926D00, 0x249200, 0x009200, 0x00B66D,
         0x009292, 0x242424, 0x000000, 0x000000,
         0xFFFFFF, 0x6DB6FF, 0x9292FF, 0xDB6DFF,
         0xFF00FF, 0xFF6DFF, 0xFF9200, 0xFFB600,
         0xDBDB00, 0x6DDB00, 0x00FF00, 0x49FFDB,
         0x00FFFF, 0x494949, 0x000000, 0x000000,
         0xFFFFFF, 0xB6DBFF, 0xDBB6FF, 0xFFB6FF,
         0xFF92FF, 0xFFB6B6, 0xFFDB92, 0xFFFF49,
         0xFFFF6D, 0xB6FF49, 0x92FF6D, 0x49FFDB,
         0x92DBFF, 0x929292, 0x000000, 0x000000 }
   },
   { "yuv-v3", "FBX's YUV-V3 palette",
      { 0x666666, 0x002A88, 0x1412A7, 0x3B00A4,
         0x5C007E, 0x6E0040, 0x6C0700, 0x561D00,
         0x333500, 0x0C4800, 0x005200, 0x004C18,
         0x003E5B, 0x000000, 0x000000, 0x000000,
         0xADADAD, 0x155FD9, 0x4240FF, 0x7527FE,
         0xA01ACC, 0xB71E7B, 0xB53120, 0x994E00,
         0x6B6D00, 0x388700, 0x0D9300, 0x008C47,
         0x007AA0, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x64B0FF, 0x9290FF, 0xC676FF,
         0xF26AFF, 0xFF6ECC, 0xFF8170, 0xEA9E22,
         0xBCBE00, 0x88D800, 0x5CE430, 0x45E082,
         0x48CDDE, 0x4F4F4F, 0x000000, 0x000000,
         0xFFFFFF, 0xC0DFFF, 0xD3D2FF, 0xE8C8FF,
         0xFAC2FF, 0xFFC4EA, 0xFFCCC5, 0xF7D8A5,
         0xE4E594, 0xCFEF96, 0xBDF4AB, 0xB3F3CC,
         0xB5EBF2, 0xB8B8B8, 0x000000, 0x000000 }
   },
   { "unsaturated-final", "FBX's Unsaturated-Final palette",
      { 0x676767, 0x001F8E, 0x23069E, 0x40008E,
         0x600067, 0x67001C, 0x5B1000, 0x432500,
         0x313400, 0x074800, 0x004F00, 0x004622,
         0x003A61, 0x000000, 0x000000, 0x000000,
         0xB3B3B3, 0x205ADF, 0x5138FB, 0x7A27EE,
         0xA520C2, 0xB0226B, 0xAD3702, 0x8D5600,
         0x6E7000, 0x2E8A00, 0x069200, 0x008A47,
         0x037B9B, 0x101010, 0x000000, 0x000000,
         0xFFFFFF, 0x62AEFF, 0x918BFF, 0xBC78FF,
         0xE96EFF, 0xFC6CCD, 0xFA8267, 0xE29B26,
         0xC0B901, 0x84D200, 0x58DE38, 0x46D97D,
         0x49CED2, 0x494949, 0x000000, 0x000000,
         0xFFFFFF, 0xC1E3FF, 0xD5D4FF, 0xE7CCFF,
         0xFBC9FF, 0xFFC7F0, 0xFFD0C5, 0xF8DAAA,
         0xEBE69A, 0xD1F19A, 0xBEF7AF, 0xB6F4CD,
         0xB7F0EF, 0xB2B2B2, 0x000000, 0x000000 }
   },
   { "sony-cxa2025as-us", "Sony CXA2025AS US palette",
      { 0x585858, 0x00238C, 0x00139B, 0x2D0585,
         0x5D0052, 0x7A0017, 0x7A0800, 0x5F1800,
         0x352A00, 0x093900, 0x003F00, 0x003C22,
         0x00325D, 0x000000, 0x000000, 0x000000,
         0xA1A1A1, 0x0053EE, 0x153CFE, 0x6028E4,
         0xA91D98, 0xD41E41, 0xD22C00, 0xAA4400,
         0x6C5E00, 0x2D7300, 0x007D06, 0x007852,
         0x0069A9, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x1FA5FE, 0x5E89FE, 0xB572FE,
         0xFE65F6, 0xFE6790, 0xFE773C, 0xFE9308,
         0xC4B200, 0x79CA10, 0x3AD54A, 0x11D1A4,
         0x06BFFE, 0x424242, 0x000000, 0x000000,
         0xFFFFFF, 0xA0D9FE, 0xBDCCFE, 0xE1C2FE,
         0xFEBCFB, 0xFEBDD0, 0xFEC5A9, 0xFED18E,
         0xE9DE86, 0xC7E992, 0xA8EEB0, 0x95ECD9,
         0x91E4FE, 0xACACAC, 0x000000, 0x000000 }
   },
   { "pal", "PAL palette",
      { 0x808080, 0x0000BA, 0x3700BF, 0x8400A6,
         0xBB006A, 0xB7001E, 0xB30000, 0x912600,
         0x7B2B00, 0x003E00, 0x00480D, 0x003C22,
         0x002F66, 0x000000, 0x050505, 0x050505,
         0xC8C8C8, 0x0059FF, 0x443CFF, 0xB733CC,
         0xFE33AA, 0xFE375E, 0xFE371A, 0xD54B00,
         0xC46200, 0x3C7B00, 0x1D8415, 0x009566,
         0x0084C4, 0x111111, 0x090909, 0x090909,
         0xFEFEFE, 0x0095FF, 0x6F84FF, 0xD56FFF,
         0xFE77CC, 0xFE6F99, 0xFE7B59, 0xFE915F,
         0xFEA233, 0xA6BF00, 0x51D96A, 0x4DD5AE,
         0x00D9FF, 0x666666, 0x0D0D0D, 0x0D0D0D,
         0xFEFEFE, 0x84BFFF, 0xBBBBFF, 0xD0BBFF,
         0xFEBFEA, 0xFEBFCC, 0xFEC4B7, 0xFECCAE,
         0xFED9A2, 0xCCE199, 0xAEEEB7, 0xAAF8EE,
         0xB3EEFF, 0xDDDDDD, 0x111111, 0x111111 }
   },
   { "bmf-final2", "BMF's Final 2 palette",
      { 0x525252, 0x000080, 0x08008A, 0x2C007E,
         0x4A004E, 0x500006, 0x440000, 0x260800,
         0x0A2000, 0x002E00, 0x003200, 0x00260A,
         0x001C48, 0x000000, 0x000000, 0x000000,
         0xA4A4A4, 0x0038CE, 0x3416EC, 0x5E04DC,
         0x8C00B0, 0x9A004C, 0x901800, 0x703600,
         0x4C5400, 0x0E6C00, 0x007400, 0x006C2C,
         0x005E84, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x4C9CFF, 0x7C78FF, 0xA664FF,
         0xDA5AFF, 0xF054C0, 0xF06A56, 0xD68610,
         0xBAA400, 0x76C000, 0x46CC1A, 0x2EC866,
         0x34C2BE, 0x3A3A3A, 0x000000, 0x000000,
         0xFFFFFF, 0xB6DAFF, 0xC8CAFF, 0xDAC2FF,
         0xF0BEFF, 0xFCBCEE, 0xFAC2C0, 0xF2CCA2,
         0xE6DA92, 0xCCE68E, 0xB8EEA2, 0xAEEABE,
         0xAEE8E2, 0xB0B0B0, 0x000000, 0x000000 }
   },
   { "bmf-final3", "BMF's Final 3 palette",
      { 0x686868, 0x001299, 0x1A08AA, 0x51029A,
         0x7E0069, 0x8E001C, 0x7E0301, 0x511800,
         0x1F3700, 0x014E00, 0x005A00, 0x00501C,
         0x004061, 0x000000, 0x000000, 0x000000,
         0xB9B9B9, 0x0C5CD7, 0x5035F0, 0x8919E0,
         0xBB0CB3, 0xCE0C61, 0xC02B0E, 0x954D01,
         0x616F00, 0x1F8B00, 0x01980C, 0x00934B,
         0x00819B, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x63B4FF, 0x9B91FF, 0xD377FF,
         0xEF6AFF, 0xF968C0, 0xF97D6C, 0xED9B2D,
         0xBDBD16, 0x7CDA1C, 0x4BE847, 0x35E591,
         0x3FD9DD, 0x606060, 0x000000, 0x000000,
         0xFFFFFF, 0xACE7FF, 0xD5CDFF, 0xEDBAFF,
         0xF8B0FF, 0xFEB0EC, 0xFDBDB5, 0xF9D28E,
         0xE8EB7C, 0xBBF382, 0x99F7A2, 0x8AF5D0,
         0x92F4F1, 0xBEBEBE, 0x000000, 0x000000 }
   },
   { "smooth-fbx", "FBX's Smooth palette",
      { 0x6A6D6A, 0x001380, 0x1E008A, 0x39007A,
         0x550056, 0x5A0018, 0x4F1000, 0x3D1C00,
         0x253200, 0x003D00, 0x004000, 0x003924,
         0x002E55, 0x000000, 0x000000, 0x000000,
         0xB9BCB9, 0x1850C7, 0x4B30E3, 0x7322D6,
         0x951FA9, 0x9D285C, 0x983700, 0x7F4C00,
         0x5E6400, 0x227700, 0x027E02, 0x007645,
         0x006E8A, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x68A6FF, 0x8C9CFF, 0xB586FF,
         0xD975FD, 0xE377B9, 0xE58D68, 0xD49D29,
         0xB3AF0C, 0x7BC211, 0x55CA47, 0x46CB81,
         0x47C1C5, 0x4A4D4A, 0x000000, 0x000000,
         0xFFFFFF, 0xCCEAFF, 0xDDDEFF, 0xECDAFF,
         0xF8D7FE, 0xFCD6F5, 0xFDDBCF, 0xF9E7B5,
         0xF1F0AA, 0xDAFAA9, 0xC9FFBC, 0xC3FBD7,
         0xC4F6F6, 0xBEC1BE, 0x000000, 0x000000 }
   },
   { "composite-direct-fbx", "FBX's Composite Direct palette",
      { 0x656565, 0x00127D, 0x18008E, 0x360082,
         0x56005D, 0x5A0018, 0x4F0500, 0x381900,
         0x1D3100, 0x003D00, 0x004100, 0x003B17,
         0x002E55, 0x000000, 0x000000, 0x000000,
         0xAFAFAF, 0x194EC8, 0x472FE3, 0x6B1FD7,
         0x931BAE, 0x9E1A5E, 0x993200, 0x7B4B00,
         0x5B6700, 0x267A00, 0x008200, 0x007A3E,
         0x006E8A, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x64A9FF, 0x8E89FF, 0xB676FF,
         0xE06FFF, 0xEF6CC4, 0xF0806A, 0xD8982C,
         0xB9B40A, 0x83CB0C, 0x5BD63F, 0x4AD17E,
         0x4DC7CB, 0x4C4C4C, 0x000000, 0x000000,
         0xFFFFFF, 0xC7E5FF, 0xD9D9FF, 0xE9D1FF,
         0xF9CEFF, 0xFFCCF1, 0xFFD4CB, 0xF8DFB1,
         0xEDEAA4, 0xD6F4A4, 0xC5F8B8, 0xBEF6D3,
         0xBFF1F1, 0xB9B9B9, 0x000000, 0x000000 }
   },
   { "pvm-style-d93-fbx", "FBX's PVM Style D93 palette",
      { 0x696B63, 0x001774, 0x1E0087, 0x340073,
         0x560057, 0x5E0013, 0x531A00, 0x3B2400,
         0x243000, 0x063A00, 0x003F00, 0x003B1E,
         0x00334E, 0x000000, 0x000000, 0x000000,
         0xB9BBB3, 0x1453B9, 0x4D2CDA, 0x671EDE,
         0x98189C, 0x9D2344, 0xA03E00, 0x8D5500,
         0x656D00, 0x2C7900, 0x008100, 0x007D42,
         0x00788A, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x69A8FF, 0x9691FF, 0xB28AFA,
         0xEA7DFA, 0xF37BC7, 0xF28E59, 0xE6AD27,
         0xD7C805, 0x90DF07, 0x64E53C, 0x45E27D,
         0x48D5D9, 0x4E5048, 0x000000, 0x000000,
         0xFFFFFF, 0xD2EAFF, 0xE2E2FF, 0xE9D8FF,
         0xF5D2FF, 0xF8D9EA, 0xFADEB9, 0xF9E89B,
         0xF3F28C, 0xD3FA91, 0xB8FCA8, 0xAEFACA,
         0xCAF3F3, 0xBEC0B8, 0x000000, 0x000000 }
   },
   { "ntsc-hardware-fbx", "FBX's NTSC Hardware palette",
      { 0x6A6D6A, 0x001380, 0x1E008A, 0x39007A,
         0x550056, 0x5A0018, 0x4F1000, 0x382100,
         0x213300, 0x003D00, 0x004000, 0x003924,
         0x002E55, 0x000000, 0x000000, 0x000000,
         0xB9BCB9, 0x1850C7, 0x4B30E3, 0x7322D6,
         0x951FA9, 0x9D285C, 0x963C00, 0x7A5100,
         0x5B6700, 0x227700, 0x027E02, 0x007645,
         0x006E8A, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x68A6FF, 0x9299FF, 0xB085FF,
         0xD975FD, 0xE377B9, 0xE58D68, 0xCFA22C,
         0xB3AF0C, 0x7BC211, 0x55CA47, 0x46CB81,
         0x47C1C5, 0x4A4D4A, 0x000000, 0x000000,
         0xFFFFFF, 0xCCEAFF, 0xDDDEFF, 0xECDAFF,
         0xF8D7FE, 0xFCD6F5, 0xFDDBCF, 0xF9E7B5,
         0xF1F0AA, 0xDAFAA9, 0xC9FFBC, 0xC3FBD7,
         0xC4F6F6, 0xBEC1BE, 0x000000, 0x000000 }
   },
   { "nes-classic-fbx-fs", "FBX's NES-Classic FS palette",
      { 0x60615F, 0x000083, 0x1D0195, 0x340875,
         0x51055E, 0x56000F, 0x4C0700, 0x372308,
         0x203A0B, 0x0F4B0E, 0x194C16, 0x02421E,
         0x023154, 0x000000, 0x000000, 0x000000,
         0xA9AAA8, 0x104BBF, 0x4712D8, 0x6300CA,
         0x8800A9, 0x930B46, 0x8A2D04, 0x6F5206,
         0x5C7114, 0x1B8D12, 0x199509, 0x178448,
         0x206B8E, 0x000000, 0x000000, 0x000000,
         0xFBFBFB, 0x6699F8, 0x8974F9, 0xAB58F8,
         0xD557EF, 0xDE5FA9, 0xDC7F59, 0xC7A224,
         0xA7BE03, 0x75D703, 0x60E34F, 0x3CD68D,
         0x56C9CC, 0x414240, 0x000000, 0x000000,
         0xFBFBFB, 0xBED4FA, 0xC9C7F9, 0xD7BEFA,
         0xE8B8F9, 0xF5BAE5, 0xF3CAC2, 0xDFCDA7,
         0xD9E09C, 0xC9EB9E, 0xC0EDB8, 0xB5F4C7,
         0xB9EAE9, 0xABABAB, 0x000000, 0x000000 }
   },
   { "nescap", "RGBSource's NESCAP palette",
      { 0x646365, 0x001580, 0x1D0090, 0x380082,
         0x56005D, 0x5A001A, 0x4F0900, 0x381B00,
         0x1E3100, 0x003D00, 0x004100, 0x003A1B,
         0x002F55, 0x000000, 0x000000, 0x000000,
         0xAFADAF, 0x164BCA, 0x472AE7, 0x6B1BDB,
         0x9617B0, 0x9F185B, 0x963001, 0x7B4800,
         0x5A6600, 0x237800, 0x017F00, 0x00783D,
         0x006C8C, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x60A6FF, 0x8F84FF, 0xB473FF,
         0xE26CFF, 0xF268C3, 0xEF7E61, 0xD89527,
         0xBAB307, 0x81C807, 0x57D43D, 0x47CF7E,
         0x4BC5CD, 0x4C4B4D, 0x000000, 0x000000,
         0xFFFFFF, 0xC2E0FF, 0xD5D2FF, 0xE3CBFF,
         0xF7C8FF, 0xFEC6EE, 0xFECEC6, 0xF6D7AE,
         0xE9E49F, 0xD3ED9D, 0xC0F2B2, 0xB9F1CC,
         0xBAEDED, 0xBAB9BB, 0x000000, 0x000000 }
   },
   { "wavebeam", "nakedarthur's Wavebeam palette",
      { 0X6B6B6B, 0X001B88, 0X21009A, 0X40008C,
         0X600067, 0X64001E, 0X590800, 0X481600,
         0X283600, 0X004500, 0X004908, 0X00421D,
         0X003659, 0X000000, 0X000000, 0X000000,
         0XB4B4B4, 0X1555D3, 0X4337EF, 0X7425DF,
         0X9C19B9, 0XAC0F64, 0XAA2C00, 0X8A4B00,
         0X666B00, 0X218300, 0X008A00, 0X008144,
         0X007691, 0X000000, 0X000000, 0X000000,
         0XFFFFFF, 0X63B2FF, 0X7C9CFF, 0XC07DFE,
         0XE977FF, 0XF572CD, 0XF4886B, 0XDDA029,
         0XBDBD0A, 0X89D20E, 0X5CDE3E, 0X4BD886,
         0X4DCFD2, 0X525252, 0X000000, 0X000000,
         0XFFFFFF, 0XBCDFFF, 0XD2D2FF, 0XE1C8FF,
         0XEFC7FF, 0XFFC3E1, 0XFFCAC6, 0XF2DAAD,
         0XEBE3A0, 0XD2EDA2, 0XBCF4B4, 0XB5F1CE,
         0XB6ECF1, 0XBFBFBF, 0X000000, 0X000000 }
   },
   { "digital-prime-fbx", "FBX's Digital Prime palette",
      { 0x616161, 0x000088, 0x1F0D99, 0x371379,
         0x561260, 0x5D0010, 0x520E00, 0x3A2308,
         0x21350C, 0x0D410E, 0x174417, 0x003A1F,
         0x002F57, 0x000000, 0x000000, 0x000000,
         0xAAAAAA, 0x0D4DC4, 0x4B24DE, 0x6912CF,
         0x9014AD, 0x9D1C48, 0x923404, 0x735005,
         0x5D6913, 0x167A11, 0x138008, 0x127649,
         0x1C6691, 0x000000, 0x000000, 0x000000,
         0xFCFCFC, 0x639AFC, 0x8A7EFC, 0xB06AFC,
         0xDD6DF2, 0xE771AB, 0xE38658, 0xCC9E22,
         0xA8B100, 0x72C100, 0x5ACD4E, 0x34C28E,
         0x4FBECE, 0x424242, 0x000000, 0x000000,
         0xFCFCFC, 0xBED4FC, 0xCACAFC, 0xD9C4FC,
         0xECC1FC, 0xFAC3E7, 0xF7CEC3, 0xE2CDA7,
         0xDADB9C, 0xC8E39E, 0xBFE5B8, 0xB2EBC8,
         0xB7E5EB, 0xACACAC, 0x000000, 0x000000 }
   },
   { "magnum-fbx", "FBX's Magnum palette",
      { 0x696969, 0x00148F, 0x1E029B, 0x3F008A,
         0x600060, 0x660017, 0x570D00, 0x451B00,
         0x243400, 0x004200, 0x004500, 0x003C1F,
         0x00315C, 0x000000, 0x000000, 0x000000,
         0xAFAFAF, 0x0F51DD, 0x442FF3, 0x7220E2,
         0xA319B3, 0xAE1C51, 0xA43400, 0x884D00,
         0x676D00, 0x208000, 0x008B00, 0x007F42,
         0x006C97, 0x010101, 0x000000, 0x000000,
         0xFFFFFF, 0x65AAFF, 0x8C96FF, 0xB983FF,
         0xDD6FFF, 0xEA6FBD, 0xEB8466, 0xDCA21F,
         0xBAB403, 0x7ECB07, 0x54D33E, 0x3CD284,
         0x3EC7CC, 0x4B4B4B, 0x000000, 0x000000,
         0xFFFFFF, 0xBDE2FF, 0xCECFFF, 0xE6C2FF,
         0xF6BCFF, 0xF9C2ED, 0xFACFC6, 0xF8DEAC,
         0xEEE9A1, 0xD0F59F, 0xBBF5AF, 0xB3F5CD,
         0xB9EDF0, 0xB9B9B9, 0x000000, 0x000000 }
   },
   { "smooth-v2-fbx", "FBX's Smooth V2 palette",
      { 0x6A6A6A, 0x00148F, 0x1E029B, 0x3F008A,
         0x600060, 0x660017, 0x570D00, 0x3C1F00,
         0x1B3300, 0x004200, 0x004500, 0x003C1F,
         0x00315C, 0x000000, 0x000000, 0x000000,
         0xB9B9B9, 0x0F4BD4, 0x412DEB, 0x6C1DD9,
         0x9C17AB, 0xA71A4D, 0x993200, 0x7C4A00,
         0x546400, 0x1A7800, 0x007F00, 0x00763E,
         0x00678F, 0x010101, 0x000000, 0x000000,
         0xFFFFFF, 0x68A6FF, 0x8C9CFF, 0xB586FF,
         0xD975FD, 0xE377B9, 0xE58D68, 0xD49D29,
         0xB3AF0C, 0x7BC211, 0x55CA47, 0x46CB81,
         0x47C1C5, 0x4A4A4A, 0x000000, 0x000000,
         0xFFFFFF, 0xCCEAFF, 0xDDDEFF, 0xECDAFF,
         0xF8D7FE, 0xFCD6F5, 0xFDDBCF, 0xF9E7B5,
         0xF1F0AA, 0xDAFAA9, 0xC9FFBC, 0xC3FBD7,
         0xC4F6F6, 0xBEBEBE, 0x000000, 0x000000 }
   },
   { "nes-classic-fbx", "FBX's NES Classic palette",
      { 0x616161, 0x000088, 0x1F0D99, 0x371379,
         0x561260, 0x5D0010, 0x520E00, 0x3A2308,
         0x21350C, 0x0D410E, 0x174417, 0x003A1F,
         0x002F57, 0x000000, 0x000000, 0x000000,
         0xAAAAAA, 0x0D4DC4, 0x4B24DE, 0x6912CF,
         0x9014AD, 0x9D1C48, 0x923404, 0x735005,
         0x5D6913, 0x167A11, 0x138008, 0x127649,
         0x1C6691, 0x000000, 0x000000, 0x000000,
         0xFCFCFC, 0x639AFC, 0x8A7EFC, 0xB06AFC,
         0xDD6DF2, 0xE771AB, 0xE38658, 0xCC9E22,
         0xA8B100, 0x72C100, 0x5ACD4E, 0x34C28E,
         0x4FBECE, 0x424242, 0x000000, 0x000000,
         0xFCFCFC, 0xBED4FC, 0xCACAFC, 0xD9C4FC,
         0xECC1FC, 0xFAC3E7, 0xF7CEC3, 0xE2CDA7,
         0xDADB9C, 0xC8E39E, 0xBFE5B8, 0xB2EBC8,
         0xB7E5EB, 0xACACAC, 0x000000, 0x000000 }
      },
   { "royaltea", "Royaltea palette (PVM-2530)",
      { 0x5A6165, 0x0023A8, 0x0F17B0, 0x28129F,
         0x550B61, 0x6B0A11, 0x6E0D00, 0x5E1900,
         0x3C2402, 0x003104, 0x003508, 0x00341F,
         0x002C55, 0x000000, 0x000000, 0x000000,
         0xA7B5BC, 0x0059FF, 0x2A44FF, 0x523CF1,
         0x9F34BA, 0xB32846, 0xBB2D09, 0x9E4100,
         0x865A00, 0x246D02, 0x007312, 0x007156,
         0x0066A6, 0x000000, 0x000000, 0x000000,
         0xFFFFFF, 0x4B9FFF, 0x5A91FF, 0x867EFF,
         0xD97DFF, 0xFF95CF, 0xFF8E76, 0xF7A247,
         0xEFB412, 0x8CC51C, 0x48D04A, 0x10D197,
         0x00C9F0, 0x43484B, 0x000000, 0x000000,
         0xFFFFFF, 0xB1D9FF, 0xB1CFFF, 0xBCC8FF,
         0xE3C8FF, 0xFFD3F7, 0xFFD5CB, 0xFFDEB9,
         0xFFE5AD, 0xDBF6AF, 0xB7FBC4, 0x9CFBE6,
         0x96F7FF, 0xB1C0C7, 0x000000, 0x000000 }
   },
   { "mugicha", "Mugicha palette",
      { 0x5c6164, 0x0021a0, 0x00109c, 0x290c91,
        0x520a5c, 0x6d000e, 0x590000, 0x430d00,
        0x352200, 0x003800, 0x003d00, 0x003621,
        0x00294c, 0x000000, 0x000000, 0x000000,
        0xaab5ba, 0x0059f0, 0x2945f7, 0x523cf7,
        0xac2dc2, 0xbc095d, 0xbd2c08, 0x964200,
        0x825400, 0x007600, 0x007a00, 0x007152,
        0x0062a0, 0x000000, 0x000000, 0x000000,
        0xffffff, 0x2daaff, 0x5a92ff, 0x967eff,
        0xeb7dff, 0xff82d0, 0xff8e73, 0xf79b3d,
        0xe6b610, 0x73c40f, 0x32d141, 0x05cb88,
        0x00c8f0, 0x414548, 0x000000, 0x000000,
        0xffffff, 0xb1d9ff, 0xc8d2ff, 0xe2ccff,
        0xffccff, 0xffc6fb, 0xffd0cb, 0xffdeb9,
        0xffe5ad, 0xdbf6af, 0xb7fbc4, 0x9cfbe6,
        0x96f7ff, 0xb4c0c5, 0x000000, 0x000000 }
   }
};
=======
static bool external_palette_exist = 0;
>>>>>>> f115148 (Rebase to negativeexponent repo)

/* ========================================
 * Palette switching START
 * ======================================== */

/* Period in frames between palette switches
 * when holding RetroPad L2 + Left/Right */
#define PALETTE_SWITCH_PERIOD 30

bool palette_switch_enabled                            = false;
static bool libretro_supports_set_variable             = false;
static unsigned palette_switch_counter                 = 0;
struct retro_core_option_value *palette_opt_values     = NULL;
static const char *palette_labels[PALETTE_TOTAL_COUNT] = { 0 };

static uint32 palette_switch_get_current_index(void) {
	if (current_palette < PALETTE_COUNT)
		return current_palette + 1;

	switch (current_palette) {
	case PALETTE_INTERNAL:
		return 0;
	case PALETTE_RAW:
	case PALETTE_CUSTOM:
		return current_palette - 1;
	default:
		break;
	}

	/* Cannot happen */
	return 0;
}

static void palette_switch_init(void) {
	size_t i;
	struct retro_core_option_v2_definition *opt_defs = option_defs;
	struct retro_core_option_v2_definition *opt_def  = NULL;
#ifndef HAVE_NO_LANGEXTRA
	struct retro_core_option_v2_definition *opt_defs_intl = NULL;
	struct retro_core_option_v2_definition *opt_def_intl  = NULL;
	unsigned language                                     = 0;
#endif

	libretro_supports_set_variable = false;
	if (environ_cb(RETRO_ENVIRONMENT_SET_VARIABLE, NULL)) {
		libretro_supports_set_variable = true;
	}

	palette_switch_enabled = libretro_supports_set_variable;
	palette_switch_counter = 0;

#ifndef HAVE_NO_LANGEXTRA
	if (environ_cb(RETRO_ENVIRONMENT_GET_LANGUAGE, &language) && (language < RETRO_LANGUAGE_LAST) &&
	    (language != RETRO_LANGUAGE_ENGLISH) && options_intl[language])
		opt_defs_intl = options_intl[language]->definitions;
#endif

	/* Find option corresponding to palettes key */
	for (opt_def = opt_defs; opt_def->key; opt_def++) {
		if (!strcmp(opt_def->key, "fceumm_palette")) {
			break;
		}
	}

	/* Cache option values array for fast access
	 * when setting palette index */
	palette_opt_values = opt_def->values;

	/* Loop over all palette values and fetch
	 * palette labels for notification purposes */
	for (i = 0; i < PALETTE_TOTAL_COUNT; i++) {
		const char *value       = opt_def->values[i].value;
		const char *value_label = NULL;

		/* Check if we have a localised palette label */
#ifndef HAVE_NO_LANGEXTRA
		if (opt_defs_intl) {
			/* Find localised option corresponding to key */
			for (opt_def_intl = opt_defs_intl; opt_def_intl->key; opt_def_intl++) {
				if (!strcmp(opt_def_intl->key, "fceumm_palette")) {
					size_t j = 0;

					/* Search for current option value */
					for (;;) {
						const char *value_intl = opt_def_intl->values[j].value;

						if (!value_intl) {
							break;
						}

						if (!strcmp(value, value_intl)) {
							/* We have a match; fetch localised label */
							value_label = opt_def_intl->values[j].label;
							break;
						}

						j++;
					}

					break;
				}
			}
		}
#endif
		/* If localised palette label is unset,
		 * use label from option_defs_us or fallback
		 * to value itself */
		if (!value_label) {
			value_label = opt_def->values[i].label;
		}
		if (!value_label) {
			value_label = value;
		}

		palette_labels[i] = value_label;
	}
}

static void palette_switch_deinit(void) {
	libretro_supports_set_variable = false;
	palette_switch_enabled         = false;
	palette_switch_counter         = 0;
	palette_opt_values             = NULL;
}

static void palette_switch_set_index(uint32 palette_index) {
	struct retro_variable var = { 0 };

	if (palette_index >= PALETTE_TOTAL_COUNT)
		palette_index = PALETTE_TOTAL_COUNT - 1;

	/* Notify frontend of option value changes */
	var.key   = "fceumm_palette";
	var.value = palette_opt_values[palette_index].value;
	environ_cb(RETRO_ENVIRONMENT_SET_VARIABLE, &var);

	/* Display notification message */
	FCEUD_DispMessage(RETRO_LOG_INFO, 2000, palette_labels[palette_index]);
}

/* ========================================
 * Palette switching END
 * ======================================== */

/* ========================================
 * Stereo Filter START
 * ======================================== */

enum stereo_filter_type { STEREO_FILTER_NULL = 0, STEREO_FILTER_DELAY };
static enum stereo_filter_type current_stereo_filter = STEREO_FILTER_NULL;

#define STEREO_FILTER_DELAY_MS_DEFAULT 15.0f
typedef struct {
	int32 *samples;
	size_t samples_size;
	size_t samples_pos;
	size_t delay_count;
} stereo_filter_delay_t;
static stereo_filter_delay_t stereo_filter_delay;
static float stereo_filter_delay_ms = STEREO_FILTER_DELAY_MS_DEFAULT;

static void stereo_filter_apply_null(int32 *sound_buffer, size_t size) {
	size_t i;
	/* Each element of sound_buffer is a 16 bit mono sample
	 * stored in a 32 bit value. We convert this to stereo
	 * by copying the mono sample to both the high and low
	 * 16 bit regions of the value and casting sound_buffer
	 * to int16 when uploading to the frontend */
	for (i = 0; i < size; i++) {
		sound_buffer[i] = (sound_buffer[i] << 16) | (sound_buffer[i] & 0xFFFF);
	}
}

static void stereo_filter_apply_delay(int32 *sound_buffer, size_t size) {
	size_t delay_capacity = stereo_filter_delay.samples_size - stereo_filter_delay.samples_pos;
	size_t i;

	/* Copy current samples into the delay buffer
	 * (resizing if required) */
	if (delay_capacity < size) {
		int32 *tmp_buffer = NULL;
		size_t tmp_buffer_size;

		tmp_buffer_size = stereo_filter_delay.samples_size + (size - delay_capacity);
		tmp_buffer_size = (tmp_buffer_size << 1) - (tmp_buffer_size >> 1);
		tmp_buffer      = (int32 *)malloc(tmp_buffer_size * sizeof(int32));

		memcpy(tmp_buffer, stereo_filter_delay.samples, stereo_filter_delay.samples_pos * sizeof(int32));

		free(stereo_filter_delay.samples);

		stereo_filter_delay.samples      = tmp_buffer;
		stereo_filter_delay.samples_size = tmp_buffer_size;
	}

	for (i = 0; i < size; i++) {
		stereo_filter_delay.samples[i + stereo_filter_delay.samples_pos] = sound_buffer[i];
	}

	stereo_filter_delay.samples_pos += size;

	/* If we have enough samples in the delay
	 * buffer, mix them into the output */
	if (stereo_filter_delay.samples_pos > stereo_filter_delay.delay_count) {
		size_t delay_index    = 0;
		size_t samples_to_mix = stereo_filter_delay.samples_pos - stereo_filter_delay.delay_count;

		samples_to_mix        = (samples_to_mix > size) ? size : samples_to_mix;

		/* Perform 'null' filtering for any samples for
		 * which a delay buffer entry is unavailable */
		if (size > samples_to_mix) {
			for (i = 0; i < size - samples_to_mix; i++) {
				sound_buffer[i] = (sound_buffer[i] << 16) | (sound_buffer[i] & 0xFFFF);
			}
		}

		/* Each element of sound_buffer is a 16 bit mono sample
		 * stored in a 32 bit value. We convert this to stereo
		 * by copying the mono sample to the high (left channel)
		 * 16 bit region and the delayed sample to the low
		 * (right channel) region, casting sound_buffer
		 * to int16 when uploading to the frontend */
		for (i = size - samples_to_mix; i < size; i++) {
			sound_buffer[i] = (sound_buffer[i] << 16) | (stereo_filter_delay.samples[delay_index++] & 0xFFFF);
		}

		/* Remove the mixed samples from the delay buffer */
		memmove(stereo_filter_delay.samples,
			stereo_filter_delay.samples + samples_to_mix,
		    (stereo_filter_delay.samples_pos - samples_to_mix) * sizeof(int32));
		stereo_filter_delay.samples_pos -= samples_to_mix;
	} else {
		/* Otherwise apply the regular 'null' filter */
		for (i = 0; i < size; i++) {
			sound_buffer[i] = (sound_buffer[i] << 16) | (sound_buffer[i] & 0xFFFF);
		}
	}
}

static void (*stereo_filter_apply)(int32 *sound_buffer, size_t size) = stereo_filter_apply_null;

static void stereo_filter_deinit_delay(void) {
	if (stereo_filter_delay.samples) {
		free(stereo_filter_delay.samples);
	}

	stereo_filter_delay.samples      = NULL;
	stereo_filter_delay.samples_size = 0;
	stereo_filter_delay.samples_pos  = 0;
	stereo_filter_delay.delay_count  = 0;
}

static void stereo_filter_init_delay(void) {
	size_t initial_samples_size;

	/* Convert delay (ms) to number of samples */
	stereo_filter_delay.delay_count = (size_t)((stereo_filter_delay_ms / 1000.0f) * (float)FSettings.SndRate);

	/* Preallocate delay_count + worst case expected
	 * samples per frame to minimise reallocation of
	 * the samples buffer during runtime */
	initial_samples_size = stereo_filter_delay.delay_count + (size_t)((float)FSettings.SndRate / NES_TARGET_FPS) + 1;

	stereo_filter_delay.samples      = (int32 *)malloc(initial_samples_size * sizeof(int32));
	stereo_filter_delay.samples_size = initial_samples_size;
	stereo_filter_delay.samples_pos  = 0;

	/* Assign function pointer */
	stereo_filter_apply = stereo_filter_apply_delay;
}

static void stereo_filter_deinit(void) {
	/* Clean up */
	stereo_filter_deinit_delay();
	/* Assign default function pointer */
	stereo_filter_apply = stereo_filter_apply_null;
}

static void stereo_filter_init(void) {
	stereo_filter_deinit();

	/* Use a case statement to simplify matters
	 * if more filter types are added in the
	 * future... */
	switch (current_stereo_filter) {
	case STEREO_FILTER_DELAY:
		stereo_filter_init_delay();
		break;
	default:
		break;
	}
}

/* ========================================
 * Stereo Filter END
 * ======================================== */

/* ========================================
 * NTSC Video Filter START
 * ======================================== */

#if defined(HAVE_NTSC_FILTER)
enum nes_ntsc_type { NTSC_NONE, NTSC_COMPOSITE, NTSC_SVIDEO, NTSC_RGB, NTSC_MONOCHROME };
static enum nes_ntsc_type use_ntsc_filter = NTSC_NONE;
#endif

#if defined(HAVE_NTSC_FILTER)
#include "nes_ntsc.h"
static nes_ntsc_t *nes_ntsc = NULL;

static void ntsc_filter_deinit(void) {
	if (nes_ntsc) {
		free(nes_ntsc);
		nes_ntsc = NULL;
	}
}

static void ntsc_set_filter(void) {
	nes_ntsc_setup_t ntsc_setup = { 0 };

	ntsc_filter_deinit();

	switch (use_ntsc_filter) {
	case NTSC_COMPOSITE:
		ntsc_setup = nes_ntsc_composite;
		break;
	case NTSC_SVIDEO:
		ntsc_setup = nes_ntsc_svideo;
		break;
	case NTSC_RGB:
		ntsc_setup = nes_ntsc_rgb;
		break;
	case NTSC_MONOCHROME:
		ntsc_setup = nes_ntsc_monochrome;
		break;
	default:
		break;
	}

	if ((GameInfo && (GameInfo->type == GIT_VSUNI)) || (current_palette < PALETTE_INTERNAL) ||
	    (current_palette == PALETTE_CUSTOM)) {
		ntsc_setup.palette = (unsigned char const *)palo;
	}

	nes_ntsc = (nes_ntsc_t *)malloc(sizeof(nes_ntsc_t));
	if (nes_ntsc) {
		nes_ntsc_init(nes_ntsc, &ntsc_setup);
	}

	if (!nes_ntsc) {
		use_ntsc_filter = NTSC_NONE;
	}
}
#endif

/* ========================================
 * NTSC Video Filter END
 * ======================================== */

static void ResetPalette(void);
static void set_user_palette(void);

static void ResetPalette(void) {
	set_user_palette();
#if defined(HAVE_NTSC_FILTER)
	ntsc_set_filter();
#endif
}

/* Core options 'update display' callback */
static bool update_option_visibility(void) {
	struct retro_variable var = { 0 };
	bool updated              = false;

	/* If frontend supports core option categories,
	 * then fceumm_show_adv_system_options and
	 * fceumm_show_adv_sound_options are ignored
	 * and no options should be hidden */
	if (libretro_supports_option_categories) {
		return false;
	}

	var.key   = "fceumm_show_adv_system_options";
	var.value = NULL;

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool opt_showAdvSystemOptions_prev = opt_showAdvSystemOptions;

		opt_showAdvSystemOptions = true;
		if (strcmp(var.value, "disabled") == 0)
			opt_showAdvSystemOptions = false;

		if (opt_showAdvSystemOptions != opt_showAdvSystemOptions_prev) {
			struct retro_core_option_display option_display;
			unsigned i;
			unsigned size;
			char options_list[][25] = {
				"fceumm_overclocking",
				"fceumm_ramstate",
				"fceumm_nospritelimit",
				"fceumm_up_down_allowed",
				"fceumm_show_crosshair"
			};

			option_display.visible = opt_showAdvSystemOptions;
			size                   = sizeof(options_list) / sizeof(options_list[0]);
			for (i = 0; i < size; i++) {
				option_display.key = options_list[i];
				environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_DISPLAY, &option_display);
			}

			updated = true;
		}
	}

	var.key   = "fceumm_show_adv_sound_options";
	var.value = NULL;

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool opt_showAdvSoundOptions_prev = opt_showAdvSoundOptions;

		opt_showAdvSoundOptions = true;
		if (!strcmp(var.value, "disabled")) {
			opt_showAdvSoundOptions = false;
		}

		if (opt_showAdvSoundOptions != opt_showAdvSoundOptions_prev) {
			struct retro_core_option_display option_display;
			unsigned i;
			unsigned size;
			char options_list[][25] = {
				"fceumm_sndvolume",
				"fceumm_sndquality",
				"fceumm_sndlowpass",
				"fceumm_sndstereodelay",
				"fceumm_swapduty",
				"fceumm_apu_1",
				"fceumm_apu_2",
				"fceumm_apu_3",
				"fceumm_apu_4",
				"fceumm_apu_5"
			};

			option_display.visible = opt_showAdvSoundOptions;
			size                   = sizeof(options_list) / sizeof(options_list[0]);
			for (i = 0; i < size; i++) {
				option_display.key = options_list[i];
				environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_DISPLAY, &option_display);
			}

			updated = true;
		}
	}

	return updated;
}

static void set_variables(void) {
	struct retro_core_option_display option_display;
	unsigned index = 0;

	option_display.visible = false;

	/* Initialize main core option struct */
	memset(&option_defs_us, 0, sizeof(option_defs_us));

	/* Write common core options to main struct */
	while (option_defs[index].key) {
		memcpy(&option_defs_us[index], &option_defs[index], sizeof(struct retro_core_option_v2_definition));
		index++;
	}

	/* Append dipswitch settings to core options if available */
	set_dipswitch_variables(&environ_cb, index, option_defs_us);

	libretro_supports_option_categories = false;
	libretro_set_core_options(environ_cb, &libretro_supports_option_categories);

	/* If frontend supports core option categories,
	 * fceumm_show_adv_system_options and
	 * fceumm_show_adv_sound_options are unused
	 * and should be hidden */
	if (libretro_supports_option_categories) {
		option_display.key = "fceumm_show_adv_system_options";
		environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_DISPLAY, &option_display);

		option_display.key = "fceumm_show_adv_sound_options";
		environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_DISPLAY, &option_display);
	}
	/* If frontend does not support core option
	 * categories, core options may be shown/hidden
	 * at runtime. In this case, register 'update
	 * display' callback, so frontend can update
	 * core options menu without calling retro_run() */
	else {
		struct retro_core_options_update_display_callback update_display_cb;

		update_display_cb.callback = update_option_visibility;
		environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_UPDATE_DISPLAY_CALLBACK, &update_display_cb);
	}

	/* VS UNISystem games use internal palette regardless
	 * of user setting, so hide fceumm_palette option */
	if (GameInfo && (GameInfo->type == GIT_VSUNI)) {
		option_display.key = "fceumm_palette";
		environ_cb(RETRO_ENVIRONMENT_SET_CORE_OPTIONS_DISPLAY, &option_display);

		/* Additionally disable gamepad palette
		 * switching */
		palette_switch_enabled = false;
	}
}

/* Game Genie add-on must be enabled before
 * loading content, so we cannot parse this
 * option inside check_variables() */
static void check_game_genie_variable(void) {
	struct retro_variable var = { 0 };
	int game_genie_enabled    = 0;

	var.key = "fceumm_game_genie";

	/* Game Genie is only enabled for regular
	 * cartridges (excludes arcade content,
	 * FDS games, etc.) */
	if ((GameInfo && (GameInfo->type == GIT_CART)) &&
	    (iNESCart.mapper != 105) && /* Nintendo World Championship cart (Mapper 105)*/
	    environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) &&
	    var.value && !strcmp(var.value, "enabled")) {
		game_genie_enabled = 1;
	}

	FCEUI_SetGameGenie(game_genie_enabled);
}

/* Callback passed to FCEUI_LoadGame()
 * > Required since we must set and check
 *   core options immediately after ROM
 *   is loaded, before FCEUI_LoadGame()
 *   returns */
static void frontend_post_load_init(void) {
	set_variables();
	check_game_genie_variable();
}

static double get_aspect_ratio(void) {
	if (aspect_ratio_par == 2) {
		return (double)NES_4_3;
	} else if (aspect_ratio_par == 3) {
		return (double)NES_PP;
	} else {
		return (double)NES_8_7_PAR;
	}
}

static void set_user_palette(void) {
	unsigned i;

	palette_game_available = false;
	palette_user_available = false;
	use_raw_palette        = false;

	/* VS UNISystem uses internal palette presets regardless of options */
	if (GameInfo && (GameInfo->type == GIT_VSUNI)) {
		FCEU_ResetPalette();
	}
	/* Reset and choose between default internal or external custom palette */
	/* if palette_game_available is set to 1, external palette
	 * is loaded, else it will load default NES palette.
	 * FCEUI_SetPaletteUser() both resets the palette array to
	 * internal default palette and then chooses which one to use. */
	else if (current_palette == PALETTE_INTERNAL) {
		FCEUI_SetPaletteUser(NULL, 0);
	} else if ((current_palette == PALETTE_CUSTOM) && external_palette_exist) {
		palette_game_available = true;
		FCEUI_SetPaletteUser(NULL, 0);
	}

	/* setup raw palette */
	else if (current_palette == PALETTE_RAW) {
		pal color;
		use_raw_palette = true;
		for (i = 0; i < 64; i++) {
			color.r = (((i >> 0) & 0xF) * 255) / 15;
			color.g = (((i >> 4) & 0x3) * 255) / 3;
			color.b = 0;
			FCEUD_SetPalette(i, color.r, color.g, color.b);
		}
	}

	/* setup palette presets */
	else {
		FCEUI_SetPaletteUser(palettes[current_palette].data, 64);
	}
}

/* Set variables for NTSC(1) / PAL(2) / Dendy(3)
 * Dendy has PAL framerate and resolution, but ~NTSC timings,
 * and has 50 dummy scanlines to force 50 fps.
 */
static void set_system_region(unsigned region) {
	bool nespal = false;
	bool dendy  = false;

	switch (region) {
	case 0: /* AUTO */
		if (iNESCart.region == DENDY) {
			dendy = true;
		} else {
			nespal = iNESCart.region == NES_PAL;
		}
		break;
	case 1: /* NTSC */
		FCEUD_DispMessage(RETRO_LOG_INFO, 2000, "System: NTSC");
		break;
	case 2: /* PAL */
		nespal = true;
		FCEUD_DispMessage(RETRO_LOG_INFO, 2000, "System: PAL");
		break;
	case 3: /* Dendy */
		dendy = true;
		FCEUD_DispMessage(RETRO_LOG_INFO, 2000, "System: Dendy");
		break;
	}

	isDendy = dendy;
	FCEUI_SetVidSystem(nespal);
	ResetPalette();
}

#define VOLUME_MAX 256

static void check_variables_volume_levels(void) {
	struct {
		int channel;
		char name[25];
	} apu_channels[] = {
		{ SND_SQUARE1, "fceumm_apu_square_1" },
		{ SND_SQUARE2, "fceumm_apu_square_2" },
		{ SND_TRIANGLE, "fceumm_apu_triangle" },
		{ SND_NOISE, "fceumm_apu_noise" },
		{ SND_DMC, "fceumm_apu_dpcm" },
		{ SND_FDS, "fceumm_apu_fds" },
		{ SND_S5B, "fceumm_apu_s5b" },
		{ SND_N163, "fceumm_apu_n163" },
		{ SND_VRC6, "fceumm_apu_vrc6" },
		{ SND_VRC7, "fceumm_apu_vrc7" },
		{ SND_MMC5, "fceumm_apu_mmc5" },
	};
	struct retro_variable var = { 0 };
	int i = 0;
	int ssize = sizeof(apu_channels) / sizeof(apu_channels[0]);

	for (i = 0; i < ssize; i++) {
		int channel = apu_channels[i].channel;
		var.key     = apu_channels[i].name;
		if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
			int newval = VOLUME_MAX * atoi(var.value) / 100;
			if (FCEUI_GetSoundVolume(channel) != newval) {
				FCEUI_SetSoundVolume(channel, newval);
			}
		}
	}
}

static void check_variables(bool startup) {
	struct retro_variable var  = { 0 };
	bool stereo_filter_updated = false;
	int nes_sprites = 1, nes_background = 1;

	/* 1 = Performs only geometry update: e.g. overscans */
	/* 2 = Performs video/geometry update when needed and timing changes: e.g. region and filter change */
	int audio_video_updated = 0;

	var.key = "fceumm_sound_rate";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		int value = atoi(var.value);
		if (value != FSettings.SndRate) {
			FCEUI_Sound(value);
			audio_video_updated |= 2;
		}
	}

	var.key = "fceumm_ramstate";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "random")) {
			FSettings.RamInitState = 2;
		} else if (!strcmp(var.value, "fill $00")) {
			FSettings.RamInitState = 1;
		} else {
			FSettings.RamInitState = 0;
		}
	}

#if defined(HAVE_NTSC_FILTER)
	var.key = "fceumm_ntsc_filter";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value && GameInfo && GameInfo->type != GIT_NSF) {
		unsigned orig_value = use_ntsc_filter;
		if (!strcmp(var.value, "disabled")) {
			use_ntsc_filter = NTSC_NONE;
		} else if (!strcmp(var.value, "composite")) {
			use_ntsc_filter = NTSC_COMPOSITE;
		} else if (!strcmp(var.value, "svideo")) {
			use_ntsc_filter = NTSC_SVIDEO;
		} else if (!strcmp(var.value, "rgb")) {
			use_ntsc_filter = NTSC_RGB;
		} else if (!strcmp(var.value, "monochrome")) {
			use_ntsc_filter = NTSC_MONOCHROME;
		}
		if (use_ntsc_filter != orig_value) {
			ResetPalette();
			audio_video_updated = 2;
		}
	}
#endif /* HAVE_NTSC_FILTER */

	FCEUI_GetRenderPlanes(&nes_sprites, &nes_background);

	var.key = "fceumm_hide_sprites";
	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		nes_sprites = strcmp(var.value, "enabled");
	}

<<<<<<< HEAD
      if (!strcmp(var.value, "default"))
         current_palette = PAL_DEFAULT;
      else if (!strcmp(var.value, "raw"))
         current_palette = PAL_RAW;
      else if (!strcmp(var.value, "custom"))
         current_palette = PAL_CUSTOM;
      else if (!strcmp(var.value, "asqrealc"))
         current_palette = 0;
      else if (!strcmp(var.value, "nintendo-vc"))
         current_palette = 1;
      else if (!strcmp(var.value, "rgb"))
         current_palette = 2;
      else if (!strcmp(var.value, "yuv-v3"))
         current_palette = 3;
      else if (!strcmp(var.value, "unsaturated-final"))
         current_palette = 4;
      else if (!strcmp(var.value, "sony-cxa2025as-us"))
         current_palette = 5;
      else if (!strcmp(var.value, "pal"))
         current_palette = 6;
      else if (!strcmp(var.value, "bmf-final2"))
         current_palette = 7;
      else if (!strcmp(var.value, "bmf-final3"))
         current_palette = 8;
      else if (!strcmp(var.value, "smooth-fbx"))
         current_palette = 9;
      else if (!strcmp(var.value, "composite-direct-fbx"))
         current_palette = 10;
      else if (!strcmp(var.value, "pvm-style-d93-fbx"))
         current_palette = 11;
      else if (!strcmp(var.value, "ntsc-hardware-fbx"))
         current_palette = 12;
      else if (!strcmp(var.value, "nes-classic-fbx-fs"))
         current_palette = 13;
      else if (!strcmp(var.value, "nescap"))
         current_palette = 14;
      else if (!strcmp(var.value, "wavebeam"))
         current_palette = 15;
      else if (!strcmp(var.value, "digital-prime-fbx"))
         current_palette = 16;
      else if (!strcmp(var.value, "magnum-fbx"))
         current_palette = 17;
      else if (!strcmp(var.value, "smooth-v2-fbx"))
         current_palette = 18;
      else if (!strcmp(var.value, "nes-classic-fbx"))
         current_palette = 19;
      else if (!strcmp(var.value, "royaltea"))
         current_palette = 20;
      else if (!strcmp(var.value, "mugicha"))
         current_palette = 21;
=======
	var.key = "fceumm_hide_background";
	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		nes_background = strcmp(var.value, "enabled");
	}
>>>>>>> f115148 (Rebase to negativeexponent repo)

	FCEUI_SetRenderPlanes(nes_sprites, nes_background);

	var.key = "fceumm_palette";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned orig_value = current_palette;

		if (!strcmp(var.value, "default"))
			current_palette = PALETTE_INTERNAL;
		else if (!strcmp(var.value, "raw"))
			current_palette = PALETTE_RAW;
		else if (!strcmp(var.value, "custom"))
			current_palette = PALETTE_CUSTOM;
		else if (!strcmp(var.value, PAL_ASQREALC))
			current_palette = 0;
		else if (!strcmp(var.value, PAL_VIRTUALCONSOLE))
			current_palette = 1;
		else if (!strcmp(var.value, PAL_NESRGB))
			current_palette = 2;
		else if (!strcmp(var.value, PAL_CXA2025AS))
			current_palette = 3;
		else if (!strcmp(var.value, PAL_NESPAL))
			current_palette = 4;
		else if (!strcmp(var.value, PAL_BMF_FINAL2))
			current_palette = 5;
		else if (!strcmp(var.value, PAL_BMF_FINAL3))
			current_palette = 6;
		else if (!strcmp(var.value, PAL_NESCAP))
			current_palette = 7;
		else if (!strcmp(var.value, PAL_WAVEBEAM))
			current_palette = 8;
		else if (!strcmp(var.value, PAL_FBX_DIGITAL_PRIME))
			current_palette = 9;
		else if (!strcmp(var.value, PAL_FBX_MAGNUM))
			current_palette = 10;
		else if (!strcmp(var.value, PAL_FBX_SMOOTH_V2))
			current_palette = 11;
		else if (!strcmp(var.value, PAL_FBX_NES_CLASSIC))
			current_palette = 12;
		else if (!strcmp(var.value, PAL_ROYAL_TEA))
			current_palette = 13;
		else if (!strcmp(var.value, PAL_MUGICHA))
			current_palette = 14;

		if (current_palette != orig_value) {
			audio_video_updated = 1;
			ResetPalette();
		}
	}

	var.key = "fceumm_up_down_allowed";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool value = !strcmp(var.value, "enabled") ? true : false;
		input_allow_updown_leftright(value);
	}

	var.key = "fceumm_nospritelimit";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		int no_sprite_limit = (!strcmp(var.value, "enabled")) ? 1 : 0;
		FCEUI_DisableSpriteLimitation(no_sprite_limit);
	}

	var.key = "fceumm_overclocking";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {

		if (!strcmp(var.value, "disabled")) {
			FSettings.PPUOverclockEnabled      = 0;
			FSettings.SkipDMC7BitOverclock     = 1;
			ppu.overclock.postrender_scanlines = 0;
			ppu.overclock.vblank_scanlines     = 0;
		} else if (!strcmp(var.value, "2x-Postrender")) {
			FSettings.PPUOverclockEnabled      = 1;
			FSettings.SkipDMC7BitOverclock     = 1;
			ppu.overclock.postrender_scanlines = 266;
			ppu.overclock.vblank_scanlines     = 0;
		} else if (!strcmp(var.value, "2x-VBlank")) {
			FSettings.PPUOverclockEnabled      = 1;
			FSettings.SkipDMC7BitOverclock     = 1;
			ppu.overclock.postrender_scanlines = 0;
			ppu.overclock.vblank_scanlines     = 266;
		}

		ppu.normal_scanlines = isDendy ? 290 : 240;
		ppu.totalscanlines = ppu.normal_scanlines + (FSettings.PPUOverclockEnabled ? ppu.overclock.postrender_scanlines : 0);
	}

	var.key = "fceumm_zapper_mode";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		FCEU_ZapperSetSTMode(false);
		if (!strcmp(var.value, "mouse")) {
			input_set_zapper_mode(RetroMouse);
		} else if (!strcmp(var.value, "touchscreen")) {
			input_set_zapper_mode(RetroPointer);
		} else if (!strcmp(var.value, "stlightgun")) {
			input_set_zapper_mode(RetroSTLightgun);
			FCEU_ZapperSetSTMode(true);
		} else {
			input_set_zapper_mode(RetroLightgun); /*default setting*/
		}
	}

	var.key = "fceumm_zapper_tolerance";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		FCEU_ZapperSetTolerance(atoi(var.value));
	}

	var.key = "fceumm_zapper_trigger";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "enabled")) {
			FCEU_ZapperInvertTrigger(true);
		} else if (!strcmp(var.value, "disabled")) {
			FCEU_ZapperInvertTrigger(false);
		}
	}

	var.key = "fceumm_zapper_sensor";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "enabled")) {
			FCEU_ZapperInvertSensor(true);
		} else if (!strcmp(var.value, "disabled")) {
			FCEU_ZapperInvertSensor(false);
		}
	}

	var.key = "fceumm_arkanoid_mode";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "touchscreen")) {
			input_set_arkanoid_mode(RetroArkanoidPointer);
		} else if (!strcmp(var.value, "abs_mouse")) {
			input_set_arkanoid_mode(RetroArkanoidAbsMouse);
		} else if (!strcmp(var.value, "stelladaptor")) {
			input_set_arkanoid_mode(RetroArkanoidStelladaptor);
		} else {
			input_set_arkanoid_mode(RetroArkanoidMouse); /*default setting*/
		}
	}

	var.key = "fceumm_mouse_sensitivity";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		double value = atof(var.value);
		input_set_mousesensitivity(value);
	}

	var.key = "fceumm_show_crosshair";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "enabled")) {
			FSettings.ShowCrosshair = 1;
		} else if (!strcmp(var.value, "disabled")) {
			FSettings.ShowCrosshair = 0;
		}
	}

#if defined(PSP)
	var.key = "fceumm_overscan";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool newval = (!strcmp(var.value, "enabled"));
		if (newval != crop_overscan) {
			overscan_left   = (newval == true ? 8 : 0);
			overscan_right  = (newval == true ? 8 : 0);
			overscan_top    = (newval == true ? 8 : 0);
			overscan_bottom = (newval == true ? 8 : 0);

			crop_overscan       = newval;
			audio_video_updated = 1;
		}
	}
#else
	var.key = "fceumm_overscan_left";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned newval = atoi(var.value);
		if (newval != overscan_left) {
			overscan_left       = newval;
			audio_video_updated = 1;
		}
	}

	var.key = "fceumm_overscan_right";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned newval = atoi(var.value);
		if (newval != overscan_right) {
			overscan_right      = newval;
			audio_video_updated = 1;
		}
	}

	var.key = "fceumm_overscan_top";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned newval = atoi(var.value);
		if (newval != overscan_top) {
			overscan_top        = newval;
			audio_video_updated = 1;
		}
	}

	var.key = "fceumm_overscan_bottom";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned newval = atoi(var.value);
		if (newval != overscan_bottom) {
			overscan_bottom     = newval;
			audio_video_updated = 1;
		}
	}
#endif

	var.key = "fceumm_aspect";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		unsigned oldval = aspect_ratio_par;
		if (!strcmp(var.value, "8:7 PAR")) {
			aspect_ratio_par = 1;
		} else if (!strcmp(var.value, "4:3")) {
			aspect_ratio_par = 2;
		} else if (!strcmp(var.value, "PP")) {
			aspect_ratio_par = 3;
		}
		if (aspect_ratio_par != oldval) {
			audio_video_updated = 1;
		}
	}

	var.key = "fceumm_turbo_enable";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		if (!strcmp(var.value, "Player 1")) {
			input_enable_turbo_buttons(0, true);
		} else if (!strcmp(var.value, "Player 2")) {
			input_enable_turbo_buttons(1, true);
		} else if (!strcmp(var.value, "Players 1 and 2")) {
			input_enable_turbo_buttons(0, true);
			input_enable_turbo_buttons(1, true);
		} else {
			input_enable_turbo_buttons(0, false);
			input_enable_turbo_buttons(1, false);
		}
	}

	var.key = "fceumm_turbo_delay";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		int value = atoi(var.value);
		input_set_turbo_delay(value);
	}

	var.key = "fceumm_region";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		uint8 oldval = opt_region;
		if (!strcmp(var.value, "Auto")) {
			opt_region = 0;
		} else if (!strcmp(var.value, "NTSC")) {
			opt_region = 1;
		} else if (!strcmp(var.value, "PAL")) {
			opt_region = 2;
		} else if (!strcmp(var.value, "Dendy")) {
			opt_region = 3;
		}
		if (opt_region != oldval) {
			set_system_region(opt_region);
			audio_video_updated = 2;
		}
	}

	var.key = "fceumm_sndquality";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		uint8 oldval = sndquality;
		if (!strcmp(var.value, "Low")) {
			sndquality = 0;
		} else if (!strcmp(var.value, "High")) {
			sndquality = 1;
		} else if (!strcmp(var.value, "Very High")) {
			sndquality = 2;
		}
		if (sndquality != oldval) {
			FCEUI_SetSoundQuality(sndquality);
		}
	}

	var.key = "fceumm_sndlowpass";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		int lowpass = (!strcmp(var.value, "disabled")) ? 0 : atoi(var.value);
		FCEUI_SetLowPass(lowpass);
	}

	var.key = "fceumm_reducedmcpopping";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool newval = (!strcmp(var.value, "enabled"));
		FCEUI_ReduceDmcPopping(newval);
	}

	var.key = "fceumm_sndstereodelay";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		enum stereo_filter_type filter_type = STEREO_FILTER_NULL;
		float filter_delay_ms               = STEREO_FILTER_DELAY_MS_DEFAULT;

		if (strcmp(var.value, "disabled") && (strlen(var.value) > 1)) {
			filter_type     = STEREO_FILTER_DELAY;
			filter_delay_ms = (float)atoi(var.value);

			filter_delay_ms = (filter_delay_ms < 1.0f) ? 1.0f : filter_delay_ms;
			filter_delay_ms = (filter_delay_ms > 32.0f) ? 32.0f : filter_delay_ms;
		}

		if ((filter_type != current_stereo_filter) ||
		    ((filter_type == STEREO_FILTER_DELAY) && (filter_delay_ms != stereo_filter_delay_ms))) {
			current_stereo_filter  = filter_type;
			stereo_filter_delay_ms = filter_delay_ms;
			stereo_filter_updated  = true;
		}
	}

	var.key = "fceumm_sndvolume";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		int val = (int)((float)VOLUME_MAX * atof(var.value) / 200.0f);
		FCEUI_SetSoundVolume(SND_MASTER, val);
	}

	var.key = "fceumm_swapduty";

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value) {
		bool newval = (!strcmp(var.value, "enabled"));
		FSettings.SwapDutyCycles = newval;
	}

	if ((stereo_filter_updated || (audio_video_updated == 2)) && !startup) {
		stereo_filter_init();
	}

	if (audio_video_updated && !startup) {
		struct retro_system_av_info av_info;

		retro_get_system_av_info(&av_info);
		if (audio_video_updated == 2) {
			environ_cb(RETRO_ENVIRONMENT_SET_SYSTEM_AV_INFO, &av_info);
		} else {
			environ_cb(RETRO_ENVIRONMENT_SET_GEOMETRY, &av_info);
		}
	}

	check_variables_volume_levels();
	check_dipswitch_variables();
	update_option_visibility();
}

void input_palette_switch(bool palette_next, bool palette_prev) {
	if (palette_prev || palette_next) {
		if (palette_switch_counter == 0) {
			unsigned new_palette_index = palette_switch_get_current_index();

			if (palette_prev) {
				if (new_palette_index > 0) {
					new_palette_index--;
				} else {
					new_palette_index = PALETTE_TOTAL_COUNT - 1;
				}
			} else { /* palette_next */
				if (new_palette_index < PALETTE_TOTAL_COUNT - 1) {
					new_palette_index++;
				} else {
					new_palette_index = 0;
				}
			}

			palette_switch_set_index(new_palette_index);
		}

		palette_switch_counter++;
		if (palette_switch_counter >= PALETTE_SWITCH_PERIOD) {
			palette_switch_counter = 0;
		}
	} else {
		palette_switch_counter = 0;
	}
}

#if defined(PSP)
static void retro_run_blit_psp(uint8 *gfx) {
	static unsigned int __attribute__((aligned(16))) d_list[32];
	void *texture_vram_p = NULL;

	unsigned width  = 256;
	unsigned height = 240;

	int x, y;

	if (crop_overscan) {
		width -= 16;
		height -= 16;
	}
	texture_vram_p = (void *)(0x44200000 - (256 * 256)); /* max VRAM address - frame size */

	sceKernelDcacheWritebackRange(retro_palette, 256 * 2);
	sceKernelDcacheWritebackRange(gfx, 256 * 240);

	sceGuStart(GU_DIRECT, d_list);

	/* sceGuCopyImage doesnt seem to work correctly with GU_PSM_T8
	 * so we use GU_PSM_4444 ( 2 Bytes per pixel ) instead
	 * with half the values for pitch / width / x offset
	 */
	if (crop_overscan)
		sceGuCopyImage(GU_PSM_4444, 4, 4, 120, 224, 128, gfx, 0, 0, 128, texture_vram_p);
	else
		sceGuCopyImage(GU_PSM_4444, 0, 0, 128, 240, 128, gfx, 0, 0, 128, texture_vram_p);

	sceGuTexSync();
	sceGuTexImage(0, 256, 256, 256, texture_vram_p);
	sceGuTexMode(GU_PSM_T8, 0, 0, GU_FALSE);
	sceGuTexFunc(GU_TFX_REPLACE, GU_TCC_RGB);
	sceGuDisable(GU_BLEND);
	sceGuClutMode(GU_PSM_5650, 0, 0xFF, 0);
	sceGuClutLoad(32, retro_palette);

	sceGuFinish();

	video_cb(texture_vram_p, width, height, 256);
}
#elif defined(PS2)

static void retro_run_blit_ps2(uint8 *gfx) {
	unsigned width  = 256;
	unsigned height = 240;
	unsigned pitch  = 512;

	uint32 *buf = (uint32 *)RETRO_HW_FRAME_BUFFER_VALID;

	if (!ps2) {
		if (!environ_cb(RETRO_ENVIRONMENT_GET_HW_RENDER_INTERFACE, (void **)&ps2) || !ps2) {
			FCEU_printf(" Failed to get HW rendering interface!\n");
			return;
		}

		if (ps2->interface_version != RETRO_HW_RENDER_INTERFACE_GSKIT_PS2_VERSION) {
			FCEU_printf(" HW render interface mismatch, expected %u, got %u!\n",
			    RETRO_HW_RENDER_INTERFACE_GSKIT_PS2_VERSION, ps2->interface_version);
			return;
		}

		ps2->coreTexture->Width   = width;
		ps2->coreTexture->Height  = height;
		ps2->coreTexture->PSM     = GS_PSM_T8;
		ps2->coreTexture->ClutPSM = GS_PSM_CT16;
		ps2->coreTexture->Filter  = GS_FILTER_LINEAR;
		ps2->padding = (struct retro_hw_ps2_insets) { (float)overscan_top, (float)overscan_left, (float)overscan_bottom,
			(float)overscan_right };
	}

	ps2->coreTexture->Clut = (u32 *)retro_palette;
	ps2->coreTexture->Mem  = (u32 *)gfx;

	video_cb(buf, width, height, pitch);
}
#else
#if defined(HAVE_NTSC_FILTER)
static void retro_run_blit_ntsc(uint8 *gfx, uint8 *emp) {
	static unsigned burst_count = 0;
	static unsigned burst_phase = 0;
	double div = 1.5f;

	nes_ntsc_blit(nes_ntsc,
		(NES_NTSC_IN_T const *)gfx,
		(NES_NTSC_IN_T const *)emp,
		NES_WIDTH, burst_phase,
		NES_WIDTH, NES_HEIGHT, fceu_video_out, NTSC_WIDTH * sizeof(Bpp_t));

	burst_phase = (unsigned)((double)burst_count / div);
	burst_count = (burst_count + 1) % 3;

	video_cb(fceu_video_out + ((overscan_left * 9) / 4) + (overscan_top * NTSC_WIDTH),
		NTSC_WIDTH - (((overscan_left + overscan_right) * 9) / 4),
		NES_HEIGHT - overscan_top - overscan_bottom,
		NTSC_WIDTH * sizeof(Bpp_t));
}
#endif /* HAVE_NTSC_FILTER */

static INLINE int get_pixel_color(const uint8 *in, const uint8 *inD) {
	uint8 pixel = *in, deemp = *inD;
	int color = retro_palette[pixel];

	if (use_raw_palette) {
		return retro_palette[(pixel & 0x3F) | (deemp * 4)];
	} else if (deemp) {
		return retro_palette[256 + (pixel & 0x3F) + (deemp * 64)];
	}
	return color;
}

static void retro_run_blit(uint8 *gfx, uint8 *emp) {
	int width  = NES_WIDTH - overscan_left - overscan_right;
	int height = NES_HEIGHT - overscan_top - overscan_bottom;
	int x = 0, y = 0;

	Bpp_t *out_scanline      = fceu_video_out;
	const uint8 *in_scanline = gfx + overscan_left + overscan_top * NES_WIDTH;
	const uint8 *in_emp      = emp + overscan_left + overscan_top * NES_WIDTH;

	for (y = height; --y >= 0; out_scanline += width, in_scanline += NES_WIDTH, in_emp += NES_WIDTH) {
		for (x = 0; x < width; x++) {
			out_scanline[x] = get_pixel_color(&in_scanline[x], &in_emp[x]);
		}
	}

	video_cb(fceu_video_out, width, height, width * sizeof(Bpp_t));
}
#endif

static bool checkGG(char c) {
	static const char lets[16] = { 'A', 'P', 'Z', 'L', 'G', 'I', 'T', 'Y', 'E', 'O', 'X', 'U', 'K', 'S', 'V', 'N' };
	int x;

	for (x = 0; x < 16; x++) {
		if (lets[x] == toupper(c)) {
			return true;
		}
	}
	return false;
}

static bool GGisvalid(const char *code) {
	size_t len = strlen(code);
	uint32 i;

	if (len != 6 && len != 8) {
		return false;
	}

	for (i = 0; i < len; i++) {
		if (!checkGG(code[i])) {
			return false;
		}
	}
	return true;
}

/* Start of Libretro API */

void retro_set_environment(retro_environment_t cb) {
	struct retro_vfs_interface_info vfs_iface_info;
	static const struct retro_system_content_info_override content_overrides[] = {
		{
		    "fds|nes|unf|unif", /* extensions */
		    false,              /* need_fullpath */
		    false               /* persistent_data */
		},
		{ NULL, false, false }
	};

	environ_cb = cb;

	vfs_iface_info.required_interface_version = 1;
	vfs_iface_info.iface                      = NULL;

	if (environ_cb(RETRO_ENVIRONMENT_GET_VFS_INTERFACE, &vfs_iface_info)) {
		filestream_vfs_init(&vfs_iface_info);
	}

	environ_cb(RETRO_ENVIRONMENT_SET_CONTENT_INFO_OVERRIDE, (void *)content_overrides);
}

void retro_set_video_refresh(retro_video_refresh_t cb) {
	video_cb = cb;
}

void retro_set_audio_sample(retro_audio_sample_t cb) { }

void retro_set_audio_sample_batch(retro_audio_sample_batch_t cb) {
	audio_batch_cb = cb;
}

void retro_set_input_poll(retro_input_poll_t cb) {
	poll_cb = cb;
}

void retro_set_input_state(retro_input_state_t cb) {
	input_cb = cb;
}

void retro_init(void) {
	bool achievements = true;

	log_cb.log = default_logger;
	environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log_cb);

	environ_cb(RETRO_ENVIRONMENT_SET_SUPPORT_ACHIEVEMENTS, &achievements);

	if (environ_cb(RETRO_ENVIRONMENT_GET_INPUT_BITMASKS, NULL)) {
		libretro_supports_bitmasks = true;
	}

	environ_cb(RETRO_ENVIRONMENT_GET_MESSAGE_INTERFACE_VERSION, &libretro_msg_interface_version);

	palette_switch_init();
}

void retro_deinit(void) {
	FCEUI_CloseGame();
	FCEUI_Sound(0);
	FCEUI_Kill();
#if defined(_3DS)
	linearFree(fceu_video_out);
#elif !defined(PS2) && !defined(PSP)
	if (fceu_video_out) {
		FCEU_afree(fceu_video_out);
	}
	fceu_video_out = NULL;
#endif
#if defined(PS2)
	ps2 = NULL;
#endif
	libretro_supports_bitmasks     = false;
	libretro_msg_interface_version = 0;
	dipswitch_close();
#if defined(HAVE_NTSC_FILTER)
	ntsc_filter_deinit();
#endif
	palette_switch_deinit();
	stereo_filter_deinit();
}

unsigned retro_api_version(void) {
	return RETRO_API_VERSION;
}

void retro_get_system_info(struct retro_system_info *info) {
	info->need_fullpath    = true;
	info->valid_extensions = "fds|nes|unf|unif";
#ifdef GIT_VERSION
	info->library_version = "(SVN)" GIT_VERSION;
#else
	info->library_version = "(SVN)";
#endif
	info->library_name  = "FCEUmm";
	info->block_extract = false;
}

void retro_get_system_av_info(struct retro_system_av_info *info) {
	info->geometry.base_width = NES_WIDTH - overscan_left - overscan_right;
	info->geometry.base_height = NES_HEIGHT - overscan_top - overscan_bottom;
#if defined(HAVE_NTSC_FILTER)
	info->geometry.max_width = NTSC_WIDTH;
#else
	info->geometry.max_width = NES_WIDTH;
#endif
	info->geometry.max_height = NES_HEIGHT;
	info->geometry.aspect_ratio = get_aspect_ratio();
	info->timing.fps = NES_TARGET_FPS;
	info->timing.sample_rate = (double)FSettings.SndRate;
}

void retro_set_controller_port_device(unsigned port, unsigned device) {
	if (port < 5) {
		input_set_controller_port_device(port, device);
	}
}

void retro_reset(void) {
	FCEUI_ResetNES();
}

void retro_run(void) {
	uint8 *gfx;
	uint8 *emp;
	int32 *sound;
	int32 ssize;
	bool updated = false;

	poll_cb();

	if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE_UPDATE, &updated) && updated) {
		check_variables(false);
	}

	input_update(&input_cb);
	FCEUI_Emulate(&gfx, &emp, &sound, &ssize, 0);

#if defined(PSP)
	retro_run_blit_psp(gfx);
#elif defined(PS2)
	retro_run_blit_ps2(gfx);
#else
#if defined(HAVE_NTSC_FILTER)
	if (use_ntsc_filter != NTSC_NONE) {
		retro_run_blit_ntsc(gfx, emp);
	} else
#endif /* HAVE_NTSC_FILTER */
	{
		retro_run_blit(gfx, emp);
	}
#endif

	stereo_filter_apply(sound, ssize);
	audio_batch_cb((const int16 *)sound, ssize);
}

size_t retro_serialize_size(void) {
	if (serialize_size == 0) {
		/* Something arbitrarily big.*/
		uint8 *buffer = (uint8 *)malloc(1000000);
		memstream_set_buffer(buffer, 1000000);

		FCEUSS_Save_Mem();
		serialize_size = memstream_get_last_size();
		free(buffer);
	}

	return serialize_size;
}

bool retro_serialize(void *data, size_t size) {
	/* Cannot save state while Game Genie
	 * screen is open */
	if (geniestage == 1) {
		return false;
	}

	if (size != retro_serialize_size()) {
		return false;
	}

	memstream_set_buffer((uint8 *)data, size);
	FCEUSS_Save_Mem();
	return true;
}

bool retro_unserialize(const void *data, size_t size) {
	/* Cannot load state while Game Genie
	 * screen is open */
	if (geniestage == 1) {
		return false;
	}

	if (size != retro_serialize_size()) {
		return false;
	}

	memstream_set_buffer((uint8 *)data, size);
	FCEUSS_Load_Mem();
	return true;
}

void retro_cheat_reset(void) {
	FCEU_ResetCheats();
}

void retro_cheat_set(unsigned index, bool enabled, const char *code) {
	char name[256];
	char temp[256];
	char *codepart;
	uint16 a;
	uint8 v;
	int c;
	int type = 1;

	if (code == NULL) {
		return;
	}

	sprintf(name, "N/A");
	strcpy(temp, code);
	codepart = strtok(temp, "+,;._ ");

	while (codepart) {
		if ((strlen(codepart) == 7) && (codepart[4] == ':')) {
			/* raw code in xxxx:xx format */
			log_cb.log(RETRO_LOG_DEBUG, "Cheat code added: '%s' (Raw)\n", codepart);
			codepart[4] = '\0';
			a           = strtoul(codepart, NULL, 16);
			v           = strtoul(codepart + 5, NULL, 16);
			c           = -1;
			/* Zero-page addressing modes don't go through the normal read/write handlers in FCEU, so
			 * we must do the old hacky method of RAM cheats. */
			if (a < 0x0100) {
				type = 0;
			}
			FCEUI_AddCheat(name, a, v, c, type);
		} else if ((strlen(codepart) == 10) && (codepart[4] == '?') && (codepart[7] == ':')) {
			/* raw code in xxxx?xx:xx */
			log_cb.log(RETRO_LOG_DEBUG, "Cheat code added: '%s' (Raw)\n", codepart);
			codepart[4] = '\0';
			codepart[7] = '\0';
			a           = strtoul(codepart, NULL, 16);
			v           = strtoul(codepart + 8, NULL, 16);
			c           = strtoul(codepart + 5, NULL, 16);
			/* Zero-page addressing modes don't go through the normal read/write handlers in FCEU, so
			 * we must do the old hacky method of RAM cheats. */
			if (a < 0x0100) {
				type = 0;
			}
			FCEUI_AddCheat(name, a, v, c, type);
		} else if (GGisvalid(codepart) && FCEUI_DecodeGG(codepart, &a, &v, &c)) {
			FCEUI_AddCheat(name, a, v, c, type);
			log_cb.log(RETRO_LOG_DEBUG, "Cheat code added: '%s' (GG)\n", codepart);
		} else if (FCEUI_DecodePAR(codepart, &a, &v, &c, &type)) {
			FCEUI_AddCheat(name, a, v, c, type);
			log_cb.log(RETRO_LOG_DEBUG, "Cheat code added: '%s' (PAR)\n", codepart);
		} else {
			log_cb.log(RETRO_LOG_DEBUG, "Invalid or unknown code: '%s'\n", codepart);
		}
		codepart = strtok(NULL, "+,;._ ");
	}
}

static void check_system_specs(void) {
	/* TODO - when we get it running at fullspeed on PSP, set to 4 */
	unsigned level = 5;
	environ_cb(RETRO_ENVIRONMENT_SET_PERFORMANCE_LEVEL, &level);
}

static void init_blit_buffer(void) {
#if defined(_3DS)
	fceu_video_out = (uint16 *)linearMemAlign(256 * 240 * sizeof(uint16), 128);
#elif !defined(PS2) && !defined(PSP) /* PS2 targets uses hw buffers for video */
#if defined(HAVE_NTSC_FILTER)
#define FB_WIDTH  NTSC_WIDTH
#define FB_HEIGHT NES_HEIGHT
#else /* !HAVE_NTSC_FILTER */
#define FB_WIDTH  NES_WIDTH
#define FB_HEIGHT NES_HEIGHT
#endif
	fceu_video_out = (Bpp_t *)FCEU_amalloc(FB_WIDTH * FB_HEIGHT * sizeof(Bpp_t));
#endif /* !PS2 */
}

static void set_memory_maps(void) {
	size_t desc_base = 64;
	struct retro_memory_descriptor descs[64 + 4] = { 0 };
	struct retro_memory_map mmaps = { 0 };
	int i, j;

	for (i = 0, j = 0; j < (int)desc_base; j++) {
		if (MMapPtrs[j] != NULL) {
			struct retro_memory_descriptor *tmpdesc = &descs[i++];
			tmpdesc->ptr = MMapPtrs[j];
			tmpdesc->start = j * 1024;
			tmpdesc->len = 1024;
			tmpdesc->select = 0;
			if (tmpdesc->start < 0x2000) {
				tmpdesc->addrspace = "RAM";
			} else if (tmpdesc->start < 0x4000) {
				tmpdesc->addrspace = "PPU";
			} else if (tmpdesc->start < 0x4020) {
				tmpdesc->addrspace = "APU/IO";
			} else {
				tmpdesc->addrspace = "WRAM/CART";
			}
		}
	}
	/* This doesn't map in 2004--2007 but those aren't really
	 * worthwhile to read from on a vblank anyway
	 */
	descs[i].flags = 0;
	descs[i].ptr = PPU;
	descs[i].offset = 0;
	descs[i].start = 0x2000;
	descs[i].select = 0;
	descs[i].disconnect = 0;
	descs[i].len = 4;
	descs[i].addrspace = "PPUREG";
	i++;
	/* In the future, it would be good to map pattern tables 1 and 2,
	 * but these must be remapped often
	 */
	/* descs[i] = (struct retro_memory_descriptor){0, ????, 0, 0x0000 | PPU_BIT,
	 * PPU_BIT, PPU_BIT, 0x1000, "PAT0"}; */
	/* i++; */
	/* descs[i] = (struct retro_memory_descriptor){0, ????, 0, 0x1000 | PPU_BIT,
	 * PPU_BIT, PPU_BIT, 0x1000, "PAT1"}; */
	/* i++; */
	/* Likewise it would be better to use "vnapage" for this but
	 * RetroArch API is inconvenient for handles like that, so we'll
	 * just blithely assume the client will handle mapping and that
	 * we'll ignore those carts that have extra NTARAM.
	 */
	descs[i].flags = 0;
	descs[i].ptr = NTARAM;
	descs[i].offset = 0;
	descs[i].start = PPU_BIT | 0x2000;
	descs[i].select = PPU_BIT;
	descs[i].disconnect = PPU_BIT;
	descs[i].len = 0x1000;
	descs[i].addrspace = "NTARAM";
	i++;
	descs[i].flags = 0;
	descs[i].ptr = PALRAM;
	descs[i].offset = 0;
	descs[i].start = PPU_BIT | 0x3000;
	descs[i].select = PPU_BIT;
	descs[i].disconnect = PPU_BIT;
	descs[i].len = 0x020;
	descs[i].addrspace = "PALRAM";
	i++;
	/* OAM doesn't really live anywhere in address space so I'll put it at
	 * 0x4000. */
	descs[i].flags = 0;
	descs[i].ptr = SPRAM;
	descs[i].offset = 0;
	descs[i].start = PPU_BIT | 0x4000;
	descs[i].select = PPU_BIT;
	descs[i].disconnect = PPU_BIT;
	descs[i].len = 0x100;
	descs[i].addrspace = "OAM";
	i++;
	mmaps.descriptors = descs;
	mmaps.num_descriptors = i;

	environ_cb(RETRO_ENVIRONMENT_SET_MEMORY_MAPS, &mmaps);
}

bool retro_load_game(const struct retro_game_info *info) {
	const char *system_dir = NULL;
	enum retro_pixel_format rgb565;

	struct retro_game_info_ext *info_ext = NULL;
	const uint8 *content_data          = NULL;
	size_t content_size                  = 0;
	char content_path[2048]              = { 0 };

#if defined(FRONTEND_SUPPORTS_RGB565)
	rgb565 = RETRO_PIXEL_FORMAT_RGB565;
	if (environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &rgb565))
		log_cb.log(RETRO_LOG_INFO, " Frontend supports RGB565 - will use that instead of XRGB1555.\n");
#elif defined(FRONTEND_SUPPORTS_ARGB888)
	rgb565 = RETRO_PIXEL_FORMAT_XRGB8888;
	if (environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &rgb565))
		log_cb.log(RETRO_LOG_INFO, " Frontend supports xRGB888 - will use that instead of XRGB1555.\n");
#endif

	if (environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &system_dir) && system_dir) {
		FCEUI_SetBaseDirectory(system_dir);
	}

	/* Attempt to fetch extended game info */
	if (environ_cb(RETRO_ENVIRONMENT_GET_GAME_INFO_EXT, &info_ext) && info_ext) {
		content_data = (const uint8 *)info_ext->data;
		content_size = info_ext->size;

		if (info_ext->file_in_archive) {
			/* We don't have a 'physical' file in this
			 * case, but the core still needs a filename
			 * in order to detect the region of iNES v1.0
			 * ROMs. We therefore fake it, using the content
			 * directory, canonical content name, and content
			 * file extension */
			snprintf(content_path, sizeof(content_path), "%s%c%s.%s", info_ext->dir, PATH_DEFAULT_SLASH_C(),
			    info_ext->name, info_ext->ext);
		} else {
			strlcpy(content_path, info_ext->full_path, sizeof(content_path));
		}
	} else {
		if (!info || string_is_empty(info->path)) {
			return false;
		}

		strlcpy(content_path, info->path, sizeof(content_path));
	}

	check_system_specs();

	init_blit_buffer();
	if (!FCEUI_Initialize()) {
		return false;
	}

	/* initialize some of the default variables */
	sndquality = -1;
	opt_region = -1;
	isDendy  = false;

	/* Wii: initialize this or else last variable is passed through
	 * when loading another rom causing save state size change. */
	serialize_size = 0;

	set_variables();
	check_variables(true);

	FCEUI_SetSoundVolume(SND_MASTER, 100);
	FCEUI_Sound(44100);

	if (!(FCEUI_LoadGame(content_path, content_data, content_size, frontend_post_load_init))) {
		return false;
	}

	external_palette_exist = palette_game_available ? true : false;
	if (external_palette_exist) {
		FCEU_printf(" Loading custom palette: %s%cnes.pal\n", (char *)system_dir, PATH_DEFAULT_SLASH_C());
	}
	current_palette = 0;

	check_variables(true);
	stereo_filter_init();

	input_init_env(&environ_cb);
	input_set_defaults();
	input_update_descriptors();

	set_memory_maps();

	return true;
}

bool retro_load_game_special(unsigned game_type, const struct retro_game_info *info, size_t num_info) {
	return false;
}

void retro_unload_game(void) {
	FCEUI_CloseGame();
#if defined(_3DS)
	if (fceu_video_out) {
		linearFree(fceu_video_out);
	}
#elif !defined(PS2) && !defined(PSP)
	if (fceu_video_out) {
		FCEU_afree(fceu_video_out);
	}
	fceu_video_out = NULL;
#endif
#if defined(PS2)
	ps2 = NULL;
#endif
#if defined(HAVE_NTSC_FILTER)
	ntsc_filter_deinit();
#endif
}

unsigned retro_get_region(void) {
	return FSettings.PAL ? RETRO_REGION_PAL : RETRO_REGION_NTSC;
}

void *retro_get_memory_data(unsigned type) {
	switch (type) {
	case RETRO_MEMORY_SAVE_RAM:
		if (GameInfo->type == GIT_FDS) {
			return FDSROM_ptr();
		}
		if (iNESCart.SaveGame[0]) {
			return iNESCart.SaveGame[0];
		}
		break;
	case RETRO_MEMORY_SYSTEM_RAM:
		return RAM;
	}

	return NULL;
}

size_t retro_get_memory_size(unsigned type) {
	switch (type) {
	case RETRO_MEMORY_SAVE_RAM:
		if (GameInfo->type == GIT_FDS) {
			return FDSROM_size();
		}
		if (iNESCart.SaveGameLen[0]) {
			return iNESCart.SaveGameLen[0];
		}
		break;
	case RETRO_MEMORY_SYSTEM_RAM:
		return RAM_SIZE;
	}

	return 0;
}
