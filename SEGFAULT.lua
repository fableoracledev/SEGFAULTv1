--[[
    Script Name: SEGFAULT
    Platform: Gamesense (Skeet) CS:GO
    Description: Clean UI + Config System + Fast Ladder + Viewmodel + Thirdperson + Dynamic Min-Damage + Aspect Ratio + Hitmarker + Tesla + Custom HP Bar + Advanced Hybrid Resolver + Jumpscout Fix + Hitchance Override + Interactive Weapon Grid Cards + Unsafe Recharge + DT Fix on Incoming Peek + Advanced Defensive (Break LC) Engine + Early Quick Stop on Defensive + Reworked Smart On-Land & In-Air Autostop + Clean Multi-Step Prediction (Adaptive Ping & Lerp Engine) + Draggable 8-Style Rage Debug + 3D Hitbox Visualizer + Round Accuracy Stats + DT Telemetry Bar + Iconified Grouped UI + Clean Telemetry Watermark & Keybinds (Reflux RGBA Anti-Aliased Engine)
    Note: UI located in LUA -> B
]]--

if _G.SEGFAULT_INITIALIZED then
    client.color_log(255, 200, 0, "[SEGFAULT] Reloading script instance...")
end
_G.SEGFAULT_INITIALIZED = true

local vector = require "vector"
local base64 = require "gamesense/base64"
local msgpack = require "gamesense/msgpack"
local clipboard = require "gamesense/clipboard"
local antiaim_funcs = try_require and pcall(require, "gamesense/antiaim_funcs") or require("gamesense/antiaim_funcs")
local ffi = require("ffi")

local math_max, math_min, math_abs, math_floor, math_ceil = math.max, math.min, math.abs, math.floor, math.ceil
local math_sqrt, math_atan2, math_deg, math_rad, math_cos, math_sin = math.sqrt, math.atan2, math.deg, math.rad, math.cos, math.sin
local string_format, string_lower, string_upper = string.format, string.lower, string.upper
local ui_get, ui_set, ui_set_visible = ui.get, ui.set, ui.set_visible
local entity_get_local_player, entity_get_players, entity_get_prop, entity_is_alive, entity_is_dormant = entity.get_local_player, entity.get_players, entity.get_prop, entity.is_alive, entity.is_dormant
local renderer_text, renderer_rectangle, renderer_gradient, renderer_indicator = renderer.text, renderer.rectangle, renderer.gradient, renderer.indicator

local DATABASE_KEY = "segfault_db_v1051_grid"
local hitgroup_names = { 'Generic', 'Head', 'Chest', 'Stomach', 'Left arm', 'Right arm', 'Left leg', 'Right leg', 'Neck', '?', 'Gear' }

local state = {
    was_active = false,
    cvar_cache = {},
    hc_cache = nil,
    mindmg_cache = nil,
    dt_fix_applied = false,
    dt_saved_sp = nil,
    was_in_air = false,
    land_stop_until = 0,
    last_shot_tick = 0,
    last_hand = nil,
    defensive_records = {},
    qs_forced_early = false,
    saved_qs_options = nil,
    baim_overridden_ents = {},
    sp_overridden_ents = {},
    jc_overridden_ents = {},
    auto_baim_active = false,
    peek_fire_window_until = 0,
    last_move_tick = 0,
    hitmarker_alpha = 0,
    hitmarker_time = 0,
    jc_currently_resolving = false,
    jc_active_target_name = nil,
    jc_active_target_desync = 0,
    jc_active_mode_str = "Native",
    hp_players = {},
    log_notifications = {},
    fps_accum = 0,
    last_fps = 0,
    current_distance = 0,
    scopedFraction = 0,
    is_dragging = false,
    drag_offset_x = 0,
    drag_offset_y = 0,
    kb_is_dragging = false,
    kb_drag_offset_x = 0,
    kb_drag_offset_y = 0,
    panel_w = 240,
    panel_h = 95,
    last_mouse_down = false,
    dt_charge_smooth = 1.0
}

local round_stats = {
    shots_fired = 0,
    shots_hit = 0,
    total_damage = 0,
    hitgroups = {}
}

local function reset_round_stats()
    round_stats.shots_fired = 0
    round_stats.shots_hit = 0
    round_stats.total_damage = 0
    round_stats.hitgroups = {}
    for _, name in ipairs(hitgroup_names) do
        round_stats.hitgroups[name] = 0
    end
end
reset_round_stats()

local function set_cvar_cached(cvar, val)
    local str_val = tostring(val)
    if state.cvar_cache[cvar] ~= str_val then
        client.set_cvar(cvar, str_val)
        state.cvar_cache[cvar] = str_val
    end
end

local function safe_ui_reference(tab, container, name)
    local success, r1, r2, r3, r4 = pcall(ui.reference, tab, container, name)
    if success and r1 ~= nil then
        return { r1, r2, r3, r4 }
    end
    return nil
end

local refs = {
    dt = safe_ui_reference("RAGE", "Aimbot", "Double tap"),
    os = safe_ui_reference("AA", "Other", "On shot anti-aim"),
    fs = safe_ui_reference("AA", "Anti-aimbot angles", "Freestanding"),
    sp = safe_ui_reference("RAGE", "Aimbot", "Force safe point"),
    ba = safe_ui_reference("RAGE", "Other", "Force body aim") or safe_ui_reference("RAGE", "Aimbot", "Force body aim"),
    quick_peek = safe_ui_reference("RAGE", "Other", "Quick peek assist"),
    quick_stop = safe_ui_reference("RAGE", "Other", "Quick stop"),
    quick_stop_options = safe_ui_reference("RAGE", "Other", "Quick stop options"),
    esp_hpbar = safe_ui_reference("VISUALS", "Player ESP", "Health bar"),
    esp_teammates = safe_ui_reference("VISUALS", "Player ESP", "Teammates"),
    mindmg = safe_ui_reference("RAGE", "Aimbot", "Minimum damage"),
    hitchance = safe_ui_reference("RAGE", "Aimbot", "Minimum hit chance")
}

local function normalize_yaw(yaw)
    while yaw > 180 do yaw = yaw - 360 end
    while yaw < -180 do yaw = yaw + 360 end
    return yaw
end

local function hex_color(r, g, b, a)
    return string_format("\a%02x%02x%02x%02x", r or 255, g or 255, b or 255, a or 255)
end

local function lerp(a, b, percentage)
    return a + (b - a) * percentage
end

local fs_tesla = nil
do
    pcall(ffi.cdef, [[
        typedef struct { float x,y,z; } vec3_t_sfg;
        struct tesla_info_t_sfg {
            vec3_t_sfg m_pos; vec3_t_sfg m_ang; int m_entindex; const char *m_spritename;
            float m_flbeamwidth; int m_nbeams; vec3_t_sfg m_color; float m_fltimevis; float m_flradius;
        };
        typedef void(__thiscall* FX_TeslaFn_sfg)(struct tesla_info_t_sfg&);
    ]])
    local tesla_match = client.find_signature("client_panorama.dll", "\x55\x8B\xEC\x81\xEC\xCC\xCC\xCC\xCC\x56\x57\x8B\xF9\x8B\x47\x18")
    if tesla_match ~= nil then
        fs_tesla = ffi.cast("FX_TeslaFn_sfg", tesla_match)
    end
end

local function print_logo()
    client.exec("clear")
    local ascii_art = {
        "  _____ ______ _____ ______      _    _ _   _______ ",
        " / ____|  ____/ ____|  ____/\\    | |  | | | |__   __|",
        "| (___ | |__ | |    | |__ /  \\   | |  | | |    | |   ",
        " \\___ \\|  __|| | |_ |  __///\\ \\  | |  | | |    | |   ",
        " ____) | |___| |__| | | / ____ \\| |__| | |____| |   ",
        "|_____/|______\\_____|_|/_/    \\_\\\\____/|______|_|   "
    }
    for i = 1, #ascii_art do client.color_log(255, 50, 50, ascii_art[i]) end
    client.color_log(255, 255, 255, "\n[+] Welcome to SEGFAULT (Clean Telemetry Edition)")
end

local jumpscout_fix_controller = {}
local memory_protect = {}

do
    local cast = ffi.cast
    local PATCH_ADDR = 0x43372D89
    local PAGE_EXECUTE_READWRITE = 0x40
    local original_bytes = ffi.new('uint8_t[13]', { 0xF7, 0x40, 0x04, 0x00, 0x00, 0x02, 0x00, 0x0F, 0x84, 0x94, 0x04, 0x00, 0x00 })
    local patch_bytes = ffi.new('uint8_t[13]')
    ffi.fill(patch_bytes, ffi.sizeof(patch_bytes), 0x90)

    local initialized, callbacks_registered, shut, enabled, owns_patch = false, false, false, false, false
    local max_distance = -1
    local winapi
    local old_protection = ffi.new('unsigned long[1]')

    local function resolve_winapi()
        local jmp_ecx = client.find_signature('engine.dll', '\xFF\xE1')
        local get_proc_call = client.find_signature('engine.dll', '\xFF\x15\xCC\xCC\xCC\xCC\xA3\xCC\xCC\xCC\xCC\xEB\x05')
        local get_module_call = client.find_signature('engine.dll', '\xFF\x15\xCC\xCC\xCC\xCC\x85\xC0\x74\x0B')
        if not jmp_ecx or not get_proc_call or not get_module_call then return nil end

        local get_proc_address = cast('uint32_t**', cast('uint32_t', get_proc_call) + 2)[0][0]
        local get_module_handle = cast('uint32_t**', cast('uint32_t', get_module_call) + 2)[0][0]
        local call_get_proc_address = cast('uint32_t(__fastcall*)(unsigned int, unsigned int, uint32_t, const char*)', jmp_ecx)
        local call_get_module_handle = cast('uint32_t(__fastcall*)(unsigned int, unsigned int, const char*)', jmp_ecx)
        local call_virtual_protect = cast('int(__fastcall*)(unsigned int, unsigned int, void*, unsigned long, unsigned long, unsigned long*)', jmp_ecx)

        local kernel32 = call_get_module_handle(get_module_handle, 0, 'kernel32.dll')
        if kernel32 == 0 then return nil end
        local virtual_protect = call_get_proc_address(get_proc_address, 0, kernel32, 'VirtualProtect')
        if virtual_protect == 0 then return nil end

        return {
            protect = function(address, size, protection, old_prot)
                return call_virtual_protect(virtual_protect, 0, address, size, protection, old_prot)
            end
        }
    end

    local function bytes_match(address, data, size)
        local ok, result = pcall(function()
            local ptr = cast('uint8_t*', address)
            for i = 0, size - 1 do if ptr[i] ~= data[i] then return false end end
            return true
        end)
        return ok and result
    end

    local function write_bytes(address, data, size)
        local ptr = cast('void*', address)
        if winapi.protect(ptr, size, PAGE_EXECUTE_READWRITE, old_protection) == 0 then return false end
        ffi.copy(ptr, data, size)
        winapi.protect(ptr, size, old_protection[0], old_protection)
        return true
    end

    local function apply_patch()
        local size = ffi.sizeof(original_bytes)
        if bytes_match(PATCH_ADDR, patch_bytes, size) then return true end
        if owns_patch then owns_patch = false return false end
        if not bytes_match(PATCH_ADDR, original_bytes, size) then return false end
        if not write_bytes(PATCH_ADDR, patch_bytes, size) then return false end
        owns_patch = true
        return true
    end

    local function restore_patch()
        if not initialized or not owns_patch then return end
        local size = ffi.sizeof(original_bytes)
        if bytes_match(PATCH_ADDR, patch_bytes, size) then
            write_bytes(PATCH_ADDR, original_bytes, size)
        end
        owns_patch = false
    end

    local function should_patch()
        local lp = entity_get_local_player()
        if not lp or not entity_is_alive(lp) or entity_get_prop(lp, 'm_bIsScoped') ~= 1 then return false end
        if max_distance ~= nil and max_distance >= 0 then
            local threat = client.current_threat()
            if not threat or not entity_is_alive(threat) then return false end
            local mx, my, mz = entity.get_origin(lp)
            local tx, ty, tz = entity.get_origin(threat)
            if not mx or not tx then return false end
            local dx, dy, dz = tx - mx, ty - my, tz - mz
            if math_sqrt(dx * dx + dy * dy + dz * dz) > max_distance then return false end
        end
        return true
    end

    local function update_patch()
        if shut or globals.mapname() == nil then return true end
        if not enabled or not should_patch() then restore_patch() return true end
        if apply_patch() then return true end
        enabled = false
        restore_patch()
        return false
    end

    function jumpscout_fix_controller.set_distance(value)
        if type(value) == 'number' then max_distance = value end
        return true
    end

    function jumpscout_fix_controller.set_enabled(value)
        if not value then enabled = false restore_patch() return true end
        if not initialized then
            local ok, success = pcall(function()
                winapi = resolve_winapi()
                if winapi == nil then return false end
                initialized = true
                return true
            end)
            if not (ok and success) then enabled = false return false end
        end
        enabled = true
        update_patch()
        if not callbacks_registered then
            client.set_event_callback('setup_command', update_patch)
            client.set_event_callback('paint', update_patch)
            callbacks_registered = true
        end
        return true
    end

    function jumpscout_fix_controller.shutdown()
        shut = true
        enabled = false
        restore_patch()
        pcall(client.unset_event_callback, 'setup_command', update_patch)
        pcall(client.unset_event_callback, 'paint', update_patch)
    end
end

-- =========================================================================
-- UI INITIALIZATION (LUA -> B) WITH GROUPED ICONS
-- =========================================================================
local cfg_elements = {}
local menu_refs = {}
local hc_settings = {}
local tab_elements = {}
local handle_logic

local hc_weapon_list = {"Auto Snipers", "Scout", "AWP", "Desert Eagle", "Revolver R8", "Pistols"}

do
    -- Пробел в начале имени мастер-свитча заставляет скрипт сортироваться в самом верху меню (выше всех букв A-Z)
    menu_refs.master_switch         = ui.new_checkbox("LUA", "B", " SEGFAULT")
    menu_refs.tab_selector          = ui.new_combobox("LUA", "B", "Navigation", "❖ Home", "⚔ Rage", "🎯 Aim Tools", "✦ Visual", "⚙ Misc")

    menu_refs.mindmg_boost_enable = ui.new_checkbox("LUA", "B", "Dynamic Lethal Min-Damage")
    menu_refs.mindmg_hp_threshold = ui.new_slider("LUA", "B", "Lethal HP Threshold", 10, 50, 30, true, "HP")

    -- 1. Jitter & Resolver Group
    menu_refs.jc_enable             = ui.new_checkbox("LUA", "B", "🎯 Jitter Correction (Advanced Hybrid)")
    menu_refs.jc_showtarget         = ui.new_checkbox("LUA", "B", "   ↳ Show Target Status")
    menu_refs.jc_indicator          = ui.new_checkbox("LUA", "B", "   ↳ JC Active Indicator")
    menu_refs.js_fix_enable         = ui.new_checkbox("LUA", "B", "🏹 Jumpscout Fix")
    menu_refs.js_fix_dist           = ui.new_slider("LUA", "B", "   ↳ Jumpscout Fix Distance", -1, 900, -1, true, "u", 1, {[-1] = "inf"})

    -- 2. Prediction & Combat Arbiter Group
    menu_refs.real_pred_enable     = ui.new_checkbox("LUA", "B", "🔮 Smart Peek & Ping Prediction")
    menu_refs.real_pred_adaptive   = ui.new_checkbox("LUA", "B", "   ↳ Adaptive Ping & Lerp Ticks")
    menu_refs.real_pred_mode       = ui.new_combobox("LUA", "B", "   ↳ Prediction mode", "Full Sync (Me + Enemy)", "Local Peek Only", "Enemy Movement Only")
    menu_refs.real_pred_ticks      = ui.new_slider("LUA", "B", "   ↳ Prediction ticks (Base/Max)", 1, 12, 3, true, "t")

    menu_refs.force_shot_peek       = ui.new_checkbox("LUA", "B", "⚡ Force Shot on Peek")
    menu_refs.force_shot_key        = ui.new_hotkey("LUA", "B", "   ↳ Force shot key", true)
    menu_refs.force_shot_hc_red     = ui.new_slider("LUA", "B", "   ↳ Peek HC relaxation", 0, 40, 12, true, "%")
    menu_refs.force_shot_stop       = ui.new_combobox("LUA", "B", "   ↳ Peek stop mode", "Native Early", "Vector Assist", "Off")

    -- 3. Autostop & Movement Group
    menu_refs.on_land_enable        = ui.new_checkbox("LUA", "B", "🛑 On-Land Autostop")
    menu_refs.on_land_mode          = ui.new_combobox("LUA", "B", "   ↳ On-land mode", "Smart (Only if target hittable)", "Aggressive (Any active threat)")
    menu_refs.on_land_weapons       = ui.new_multiselect("LUA", "B", "   ↳ Autostop weapons", "SSG08", "AWP", "Auto snipers", "Desert eagle", "Revolver", "Pistols", "SMG", "Shotgun", "Rifles", "Machinegun")
    
    menu_refs.in_air_stop           = ui.new_checkbox("LUA", "B", "🪂 In-Air Autostop")
    menu_refs.in_air_dist           = ui.new_slider("LUA", "B", "   ↳ In-air stop distance", 200, 1001, 1001, true, "u", 1, {[1001] = "inf"})

    -- 4. Defensive & Combat Fixes Group
    menu_refs.unsafe_recharge       = ui.new_checkbox("LUA", "B", "⚙ Unsafe Recharge")
    menu_refs.early_stop_def        = ui.new_checkbox("LUA", "B", "🛡 Early Stop Against Defensive")
    menu_refs.auto_baim_peek        = ui.new_checkbox("LUA", "B", "👤 Force Body Aim if Head Hidden")

    menu_refs.dt_fix_enable         = ui.new_checkbox("LUA", "B", "⚔ DT Fix on Incoming Peek")
    menu_refs.dt_fix_weapons        = ui.new_combobox("LUA", "B", "   ↳ DT Fix Weapons", "Auto Snipers Only", "All Snipers")
    menu_refs.dt_fix_speed          = ui.new_slider("LUA", "B", "   ↳ Peek Trigger Speed", 150, 260, 210, true, "u/s")
    menu_refs.dt_fix_hc             = ui.new_slider("LUA", "B", "   ↳ DT Peek Hitchance", 50, 95, 75, true, "%")

    -- 5. Hitchance Override Group
    menu_refs.hc_enable             = ui.new_checkbox("LUA", "B", "🎯 Hitchance Override")
    menu_refs.hc_weapon             = ui.new_combobox("LUA", "B", "   ↳ HC Weapon", "Auto Snipers", "Scout", "AWP", "Desert Eagle", "Revolver R8", "Pistols")
    menu_refs.hc_hotkey             = ui.new_hotkey("LUA", "B", "   ↳ HC Hotkey", true)
    menu_refs.hc_indicator          = ui.new_combobox("LUA", "B", "   ↳ HC Indicator text", "Off", "HC", "popadi", "HITCHANCE OVR")

    for i = 1, #hc_weapon_list do
        local w = hc_weapon_list[i]
        local is_sniper = (w == "Auto Snipers" or w == "Scout" or w == "AWP")
        local opts = {"In Air", "Hotkey", "Crouch", "Peek Assist"}
        if is_sniper then table.insert(opts, 2, "No Scope") end

        local m_opts = ui.new_multiselect("LUA", "B", "["..w.."] HC Options", unpack(opts))
        local s_items = { options = m_opts }
        cfg_elements["hc_opts_"..w] = m_opts

        for j = 1, #opts do
            local opt = opts[j]
            s_items[opt] = { val = ui.new_slider("LUA", "B", "["..w.."] "..opt.." HC", 0, 100, 0, true, "%") }
            cfg_elements["hc_val_"..w.."_"..opt] = s_items[opt].val

            if opt == "In Air" then
                s_items[opt].dmg = ui.new_slider("LUA", "B", "["..w.."] In Air Min-Damage", 0, 126, 0, true, "dmg", 1, {[0] = "Default"})
                cfg_elements["hc_dmg_air_"..w] = s_items[opt].dmg
            end
            if opt == "No Scope" then
                s_items[opt].dist = ui.new_slider("LUA", "B", "["..w.."] No Scope Dist", 5, 101, 35, true, "u", 1, {[101]="Inf"})
                cfg_elements["hc_dist_"..w] = s_items[opt].dist
            end
        end
        hc_settings[w] = s_items
    end

    -- 6. Debug Panel Group
    menu_refs.debug_panel_enable  = ui.new_checkbox("LUA", "B", "📊 Rage Debug Panel (Mouse Drag)")
    menu_refs.debug_panel_style   = ui.new_combobox("LUA", "B", "   ↳ Debug Style",
        "Clean Side Text", "Minimal Pixel (-)", "Skeet Indicators", "Compact Gradient",
        "Terminal Bracket", "Cyber HUD Bars", "Crosshair Sub-Text", "Top Status Ribbon"
    )
    menu_refs.debug_panel_x       = ui.new_slider("LUA", "B", "Debug Pos X", 2, 3840, 18, true, "px")
    menu_refs.debug_panel_y       = ui.new_slider("LUA", "B", "Debug Pos Y", 2, 2160, 420, true, "px")
    ui_set_visible(menu_refs.debug_panel_x, false)
    ui_set_visible(menu_refs.debug_panel_y, false)

    menu_refs.vis_ci_enable         = ui.new_checkbox("LUA", "B", "Crosshair Indicator")
    menu_refs.vis_ci_color          = ui.new_color_picker("LUA", "B", "Crosshair Indicator Color", 190, 190, 255, 255)
    menu_refs.vis_ci_font           = ui.new_combobox("LUA", "B", "Style", "Default", "minimal")
    menu_refs.vis_watermark_enable = ui.new_checkbox("LUA", "B", "Watermark (Clean Telemetry)")
    menu_refs.vis_keybinds_enable  = ui.new_checkbox("LUA", "B", "Keybinds Panel (Clean Telemetry)")
    menu_refs.vis_keybinds_x       = ui.new_slider("LUA", "B", "Keybinds Pos X", 0, 3840, 20, true, "px")
    menu_refs.vis_keybinds_y       = ui.new_slider("LUA", "B", "Keybinds Pos Y", 0, 2160, 500, true, "px")
    ui_set_visible(menu_refs.vis_keybinds_x, false)
    ui_set_visible(menu_refs.vis_keybinds_y, false)

    menu_refs.vis_logs_enable      = ui.new_checkbox("LUA", "B", "Screen Hit/Miss Logs")
    menu_refs.vis_logs_color       = ui.new_color_picker("LUA", "B", "Logs Color", 150, 200, 255, 255)

    menu_refs.vis_telemetry_enable = ui.new_checkbox("LUA", "B", "DT Recharge & Telemetry Bar")

    menu_refs.vis_tp_enable        = ui.new_checkbox("LUA", "B", "Thirdperson Animations")
    menu_refs.vis_tp_dist          = ui.new_slider("LUA", "B", "Thirdperson Distance", 0, 250, 100)
    menu_refs.vis_tp_zoom          = ui.new_slider("LUA", "B", "Thirdperson Zoom Out Speed", 0, 100, 25, true, "%", 1, {[0] = "Instant"})
    menu_refs.vis_tp_pitch         = ui.new_slider("LUA", "B", "Thirdperson Pitch", -360, 0, 0, true, "°")
    menu_refs.vis_tp_yaw           = ui.new_slider("LUA", "B", "Thirdperson Yaw", -360, 0, 0, true, "°")
    menu_refs.vis_tp_pitch_up      = ui.new_slider("LUA", "B", "Thirdperson Pitch Up", 0, 360, 90, true, "°")
    menu_refs.vis_tp_pitch_down    = ui.new_slider("LUA", "B", "Thirdperson Pitch Down", 0, 360, 90, true, "°")

    menu_refs.vis_vm_enable        = ui.new_checkbox("LUA", "B", "Custom Viewmodel")
    menu_refs.vis_vm_fov           = ui.new_slider("LUA", "B", "Viewmodel FOV", 54, 68, 60, true, "°")
    menu_refs.vis_vm_x             = ui.new_slider("LUA", "B", "Viewmodel X", -20, 30, 10, true, "", 0.1)
    menu_refs.vis_vm_y             = ui.new_slider("LUA", "B", "Viewmodel Y", -20, 20, 10, true, "", 0.1)
    menu_refs.vis_vm_z             = ui.new_slider("LUA", "B", "Viewmodel Z", -20, 20, -10, true, "", 0.1)
    menu_refs.vis_hand_knife       = ui.new_combobox("LUA", "B", "Knife Hand", "Left", "Right")
    menu_refs.vis_hand_weapon      = ui.new_combobox("LUA", "B", "Weapon Hand", "Left", "Right")

    menu_refs.vis_ar_enable        = ui.new_checkbox("LUA", "B", "Aspect Ratio Override")
    menu_refs.vis_ar_mode          = ui.new_combobox("LUA", "B", "Aspect Ratio Preset", "Default", "4:3", "16:10", "5:4", "Custom")
    menu_refs.vis_ar_custom        = ui.new_slider("LUA", "B", "Aspect Ratio Custom", 100, 300, 177, true, "", 0.01, {[100] = "1:1", [133] = "4:3", [160] = "16:10", [177] = "16:9", [233] = "21:9"})

    menu_refs.tesla_enable         = ui.new_checkbox("LUA", "B", "Tesla on hit")
    menu_refs.tesla_color          = ui.new_color_picker("LUA", "B", "Tesla Color", 255, 255, 255, 255)
    menu_refs.tesla_width          = ui.new_slider("LUA", "B", "Tesla width", 0, 30, 10)
    menu_refs.tesla_radius         = ui.new_slider("LUA", "B", "Tesla radius", 0, 1000, 500)
    menu_refs.tesla_beams          = ui.new_slider("LUA", "B", "Beams", 0, 100, 12)

    menu_refs.hm_enable            = ui.new_checkbox("LUA", "B", "Hitmarker")
    menu_refs.hm_color             = ui.new_color_picker("LUA", "B", "Hitmarker Color", 255, 255, 255, 255)
    menu_refs.hm_size              = ui.new_slider("LUA", "B", "Hitmarker Size", 2, 15, 6, true, "px")
    menu_refs.hm_gap               = ui.new_slider("LUA", "B", "Hitmarker Gap", 1, 10, 3, true, "px")
    menu_refs.hm_duration          = ui.new_slider("LUA", "B", "Hitmarker Duration", 10, 100, 30, true, "T", 0.01)

    menu_refs.hpbar_enable         = ui.new_checkbox("LUA", "B", "Custom Health bar")
    menu_refs.hpbar_gradient       = ui.new_checkbox("LUA", "B", "Enable Gradient")
    menu_refs.hpbar_label1         = ui.new_label("LUA", "B", "Full Health")
    menu_refs.hpbar_color1         = ui.new_color_picker("LUA", "B", "Full Health", 142, 214, 77, 255)
    menu_refs.hpbar_label2         = ui.new_label("LUA", "B", "Empty Health")
    menu_refs.hpbar_color2         = ui.new_color_picker("LUA", "B", "Empty Health", 244, 48, 87, 255)
    menu_refs.hpbar_label3         = ui.new_label("LUA", "B", "Glow")
    menu_refs.hpbar_color3         = ui.new_color_picker("LUA", "B", "Glow", 100, 48, 200, 255)

    menu_refs.misc_ladder          = ui.new_checkbox("LUA", "B", "Fast ladder")

    for k, v in pairs(menu_refs) do
        if k ~= "master_switch" and k ~= "tab_selector" and k ~= "hpbar_label1" and k ~= "hpbar_label2" and k ~= "hpbar_label3" then
            cfg_elements[k] = v
        end
    end

    ui_set(menu_refs.jc_enable, true)
    ui_set(menu_refs.jc_showtarget, true)
    ui_set(menu_refs.jc_indicator, true)
    ui_set(menu_refs.debug_panel_enable, true)
    ui_set(menu_refs.real_pred_enable, true)
    ui_set(menu_refs.real_pred_adaptive, true)
    ui_set(menu_refs.vis_telemetry_enable, true)

    ui.set_callback(menu_refs.js_fix_enable, function(c)
        local val = ui_get(c)
        if not jumpscout_fix_controller.set_enabled(val) and val then ui_set(c, false) end
    end)
    ui.set_callback(menu_refs.js_fix_dist, function(c)
        jumpscout_fix_controller.set_distance(ui_get(c))
    end)

    local buffer = ffi.new("char[?]", 0x1D)
    local ogbytes = ffi.new("char[?]", 0x1D)
    local have_original, patch_owned = false, false

    ui.set_callback(menu_refs.unsafe_recharge, function(item)
        local enabled = ui_get(item)
        if not enabled then
            if patch_owned then
                memory_protect.copy(0x433AC04B, ogbytes, 0x1D)
                patch_owned = false
            end
            return
        end
        if not have_original then
            local snapshot = memory_protect.read_bytes(0x433AC04B, 0x1D)
            if snapshot == nil then return end
            local ok = pcall(function()
                for i = 1, 0x1D do ogbytes[i - 1] = snapshot[i] end
                ffi.copy(buffer, ogbytes, 0x1D)
                ffi.fill(buffer, 0x18, 0x90)
                buffer[0x18] = 0xE9
            end)
            if not ok then return end
            have_original = true
        end
        if not patch_owned then
            memory_protect.copy(0x433AC04B, buffer, 0x1D)
            patch_owned = true
        end
    end)

    local cfg_list = ui.new_listbox("LUA", "B", "Configurations", "Default")
    local cfg_name = ui.new_textbox("LUA", "B", "Config Name")
    local saved_configs = database.read(DATABASE_KEY) or {}
    local cfg_names = {}

    local function update_config_list()
        cfg_names = {}
        for k, _ in pairs(saved_configs) do table.insert(cfg_names, tostring(k)) end
        table.sort(cfg_names)
        if #cfg_names == 0 then table.insert(cfg_names, "Default") end
        ui.update(cfg_list, cfg_names)
    end
    update_config_list()

    local function get_current_settings()
        local data = {}
        for key, ref in pairs(cfg_elements) do
            local ok, r1, r2, r3, r4 = pcall(ui_get, ref)
            if ok then data[key] = (r2 ~= nil) and {r1, r2, r3, r4} or r1 end
        end
        return data
        end

    local function apply_settings(data)
        if type(data) ~= "table" then return end
        for key, ref in pairs(cfg_elements) do
            if data[key] ~= nil then
                if type(data[key]) == "table" then pcall(ui_set, ref, unpack(data[key]))
                else pcall(ui_set, ref, data[key]) end
            end
        end
        if data["js_fix_enable"] ~= nil then
            if jumpscout_fix_controller.set_enabled(data["js_fix_enable"]) == false and data["js_fix_enable"] == true then
                ui_set(menu_refs.js_fix_enable, false)
            end
        end
        if data["js_fix_dist"] ~= nil then jumpscout_fix_controller.set_distance(data["js_fix_dist"]) end
        if handle_logic then handle_logic() end
    end

    local btn_create = ui.new_button("LUA", "B", "✚ Create / Save", function()
        local name = ui_get(cfg_name)
        if name == nil or name == "" then
            local idx = ui_get(cfg_list)
            if idx ~= nil and cfg_names[idx + 1] then name = cfg_names[idx + 1] end
        end
        if name == nil or name == "" or name == "Default" then
            client.color_log(255, 100, 100, "[SEGFAULT] Error: Empty name or cannot overwrite 'Default'.")
            return
        end
        saved_configs[name] = get_current_settings()
        database.write(DATABASE_KEY, saved_configs)
        update_config_list()
        ui_set(cfg_name, "")
        client.color_log(150, 255, 150, "[SEGFAULT] Successfully saved: '" .. name .. "'")
    end)

    local btn_load = ui.new_button("LUA", "B", "⮑ Load Selected", function()
        local name = cfg_names[ui_get(cfg_list) + 1]
        if name and saved_configs[name] then
            apply_settings(saved_configs[name])
            client.color_log(150, 255, 150, "[SEGFAULT] Loaded: '" .. name .. "'")
        else
            client.color_log(255, 100, 100, "[SEGFAULT] Failed to load configuration.")
        end
    end)

    local btn_delete = ui.new_button("LUA", "B", "✖ Delete Selected", function()
        local name = cfg_names[ui_get(cfg_list) + 1]
        if name == "Default" then return end
        if name and saved_configs[name] then
            saved_configs[name] = nil
            database.write(DATABASE_KEY, saved_configs)
            update_config_list()
            client.color_log(150, 150, 150, "[SEGFAULT] Deleted: '" .. name .. "'")
        end
    end)

    local btn_export = ui.new_button("LUA", "B", "⇡ Export (Clipboard)", function()
        local name = cfg_names[ui_get(cfg_list) + 1] or "Unknown"
        local data = get_current_settings()
        data["__cfg_name"] = name
        local packed = msgpack.pack(data)
        clipboard.set("SEGFAULT::" .. base64.encode(packed) .. "::GS")
        client.color_log(150, 255, 150, "[SEGFAULT] Copied to clipboard!")
    end)

    local btn_import = ui.new_button("LUA", "B", "⇣ Import (Clipboard)", function()
        local clip_text = clipboard.get()
        if not clip_text or clip_text == "" then return end
        local encoded = string.match(clip_text, "SEGFAULT::(.+)::GS")
        if not encoded then return end
        local data = msgpack.unpack(base64.decode(encoded))
        if data then
            local imported_name = data["__cfg_name"] or "Imported_Config"
            apply_settings(data)
            ui_set(cfg_name, imported_name)
            client.color_log(150, 255, 255, "[SEGFAULT] Imported: '" .. imported_name .. "'")
        end
    end)

    local aimtools_elements = {
        menu_refs.jc_enable, menu_refs.jc_showtarget, menu_refs.jc_indicator,
        menu_refs.js_fix_enable, menu_refs.js_fix_dist,
        menu_refs.unsafe_recharge,
        menu_refs.early_stop_def, menu_refs.auto_baim_peek,
        menu_refs.real_pred_enable, menu_refs.real_pred_adaptive, menu_refs.real_pred_mode, menu_refs.real_pred_ticks,
        menu_refs.force_shot_peek, menu_refs.force_shot_key, menu_refs.force_shot_hc_red, menu_refs.force_shot_stop,
        menu_refs.on_land_enable, menu_refs.on_land_mode, menu_refs.on_land_weapons,
        menu_refs.in_air_stop, menu_refs.in_air_dist,
        menu_refs.dt_fix_enable, menu_refs.dt_fix_weapons, menu_refs.dt_fix_speed, menu_refs.dt_fix_hc,
        menu_refs.hc_enable, menu_refs.hc_weapon, menu_refs.hc_hotkey, menu_refs.hc_indicator
    }

    for _, w_items in pairs(hc_settings) do
        table.insert(aimtools_elements, w_items.options)
        for opt, opt_item in pairs(w_items) do
            if opt ~= "options" then
                table.insert(aimtools_elements, opt_item.val)
                if opt_item.dmg then table.insert(aimtools_elements, opt_item.dmg) end
                if opt_item.dist then table.insert(aimtools_elements, opt_item.dist) end
            end
        end
    end

    table.insert(aimtools_elements, menu_refs.debug_panel_enable)
    table.insert(aimtools_elements, menu_refs.debug_panel_style)

    local visual_elements = {
        menu_refs.vis_tp_enable, menu_refs.vis_tp_dist, menu_refs.vis_tp_zoom, menu_refs.vis_tp_pitch, menu_refs.vis_tp_yaw, menu_refs.vis_tp_pitch_up, menu_refs.vis_tp_pitch_down,
        menu_refs.vis_vm_enable, menu_refs.vis_vm_fov, menu_refs.vis_vm_x, menu_refs.vis_vm_y, menu_refs.vis_vm_z, menu_refs.vis_hand_knife, menu_refs.vis_hand_weapon,
        menu_refs.vis_ci_enable, menu_refs.vis_ci_color, menu_refs.vis_ci_font, menu_refs.vis_watermark_enable, menu_refs.vis_keybinds_enable, menu_refs.vis_logs_enable, menu_refs.vis_logs_color,
        menu_refs.vis_telemetry_enable,
        menu_refs.vis_ar_enable, menu_refs.vis_ar_mode, menu_refs.vis_ar_custom,
        menu_refs.tesla_enable, menu_refs.tesla_color, menu_refs.tesla_width, menu_refs.tesla_radius, menu_refs.tesla_beams,
        menu_refs.hm_enable, menu_refs.hm_color, menu_refs.hm_size, menu_refs.hm_gap, menu_refs.hm_duration,
        menu_refs.hpbar_enable, menu_refs.hpbar_gradient, menu_refs.hpbar_label1, menu_refs.hpbar_color1, menu_refs.hpbar_label2, menu_refs.hpbar_color2, menu_refs.hpbar_label3, menu_refs.hpbar_color3
    }

    tab_elements["❖ Home"]      = { cfg_list, cfg_name, btn_create, btn_load, btn_delete, btn_export, btn_import }
    tab_elements["⚔ Rage"]      = { menu_refs.mindmg_boost_enable, menu_refs.mindmg_hp_threshold }
    tab_elements["🎯 Aim Tools"] = aimtools_elements
    tab_elements["✦ Visual"]     = visual_elements
    tab_elements["⚙ Misc"]      = { menu_refs.misc_ladder }
end

-- =========================================================================
-- NETWORK ENGINE & ADAPTIVE LERP / LATENCY CALCULATION
-- =========================================================================
local function calculate_lerp_time()
    local updaterate = tonumber(client.get_cvar("cl_updaterate")) or 64
    local min_updaterate = tonumber(client.get_cvar("sv_minupdaterate")) or 64
    local max_updaterate = tonumber(client.get_cvar("sv_maxupdaterate")) or 128
    updaterate = math_max(min_updaterate, math_min(max_updaterate, updaterate))

    local interp_ratio = tonumber(client.get_cvar("cl_interp_ratio")) or 2
    local min_ratio = tonumber(client.get_cvar("sv_client_min_interp_ratio")) or 1
    local max_ratio = tonumber(client.get_cvar("sv_client_max_interp_ratio")) or 2
    interp_ratio = math_max(min_ratio, math_min(max_ratio, interp_ratio))

    local interp = tonumber(client.get_cvar("cl_interp")) or 0.031
    return math_max(interp, interp_ratio / updaterate)
end

local function get_effective_pred_ticks()
    local base_ticks = ui_get(menu_refs.real_pred_ticks) or 3
    if not ui_get(menu_refs.real_pred_adaptive) then
        return base_ticks
    end

    local tick_int = globals.tickinterval()
    if tick_int <= 0 then return base_ticks end

    local latency = math_max(0, (client.latency() or 0) * 0.5)
    local lerp_sec = calculate_lerp_time()
    local total_delay = latency + lerp_sec

    local calculated_ticks = math_floor((total_delay / tick_int) + 0.5)
    return math_max(1, math_min(base_ticks, calculated_ticks))
end

-- =========================================================================
-- ADVANCED DEFENSIVE (BREAK LC) TRACKER & ARBITER
-- =========================================================================
local function update_defensive_tracker(ent, tickcount, tick_int)
    if not ent or not entity_is_alive(ent) or entity_is_dormant(ent) then
        state.defensive_records[ent] = nil
        return false, 0
    end

    local sim_time = entity_get_prop(ent, "m_flSimulationTime") or 0
    if sim_time == 0 then return false, 0 end

    local rec = state.defensive_records[ent]

    if not rec then
        local ox, oy, oz = entity.get_origin(ent)
        state.defensive_records[ent] = {
            last_sim = sim_time,
            last_origin = {ox or 0, oy or 0, oz or 0},
            def_until_tick = 0,
            choked_ticks = 0,
            is_active = false
        }
        return false, 0
    end

    local sim_delta = sim_time - rec.last_sim
    local sim_ticks = math_floor((sim_delta / tick_int) + 0.5)

    local ox, oy, oz = entity.get_origin(ent)
    local moved_dist = 0
    if ox and rec.last_origin then
        local dx = ox - rec.last_origin[1]
        local dy = oy - rec.last_origin[2]
        local dz = oz - rec.last_origin[3]
        moved_dist = math_sqrt(dx * dx + dy * dy + dz * dz)
    end

    local is_teleporting = (sim_ticks < 0) or (sim_ticks > 2) or (moved_dist > 68)

    if is_teleporting then
        rec.def_until_tick = tickcount + 4
        rec.choked_ticks = math_max(1, math_abs(sim_ticks))
        rec.is_active = true
    elseif tickcount > rec.def_until_tick then
        rec.is_active = false
        rec.choked_ticks = 0
    end

    rec.last_sim = sim_time
    if ox then rec.last_origin = {ox, oy, oz} end

    return rec.is_active, rec.choked_ticks
end

-- =========================================================================
-- ADVANCED HYBRID JITTER & DESYNC RESOLVER ENGINE (MAXIMUM EDITION)
-- =========================================================================
local resolver_db = {}

local rage_debug = {
    weapon_name = "None",
    weapon_ready = false,
    my_speed = 0,
    threat_ent = nil,
    threat_name = "None",
    threat_hp = 0,
    threat_dist = 0,
    threat_speed = 0,
    threat_state = "Normal",
    head_visible = false,
    cur_head_dmg = 0,
    cur_body_dmg = 0,
    pred_head_dmg = 0,
    pred_body_dmg = 0,
    base_hc = 0,
    active_hc = 0,
    hc_reason = "Native",
    base_dmg = 0,
    active_dmg = 0,
    dmg_reason = "Native",
    baim_mode = "-",
    sp_mode = "-",
    pred_status = "IDLE",
    force_shot_state = "IDLE",
    blocker_text = "WAITING",
    short_status = "IDLE",
    blocker_color = {200, 200, 200},
    early_qs_active = false,
    dt_fix_active = false
}

local function get_entity_pose_data(ent)
    local pose_11 = entity_get_prop(ent, "m_flPoseParameter", 11) or 0.5
    local pose_6 = entity_get_prop(ent, "m_flPoseParameter", 6) or 0.5
    local lby = entity_get_prop(ent, "m_flLowerBodyYawTarget") or 0
    local _, eye_yaw = entity_get_prop(ent, "m_angEyeAngles")
    
    local body_yaw = (pose_11 * 120.0) - 60.0
    local pitch_pose = (pose_6 * 180.0) - 90.0
    
    return body_yaw, pitch_pose, lby, (eye_yaw or 0)
end

local function reset_entity_resolver(ent)
    if ent then
        if state.jc_overridden_ents[ent] then
            pcall(plist.set, ent, "Force body yaw", false)
            state.jc_overridden_ents[ent] = nil
        end
        resolver_db[ent] = nil
    else
        for e, _ in pairs(state.jc_overridden_ents) do
            pcall(plist.set, e, "Force body yaw", false)
        end
        state.jc_overridden_ents = {}
        resolver_db = {}
    end
end

local function run_functional_jitter_resolver(me, current_threat, enemies)
    if not ui_get(menu_refs.jc_enable) or not enemies or #enemies == 0 then
        reset_entity_resolver()
        state.jc_currently_resolving = false
        state.jc_active_mode_str = "OFF"
        return
    end

    state.jc_currently_resolving = false
    local cur_time = globals.curtime()

    for i = 1, #enemies do
        local ent = enemies[i]
        if entity_is_alive(ent) and not entity_is_dormant(ent) then
            local sim_time = entity_get_prop(ent, "m_flSimulationTime") or 0
            local body_yaw, pitch_pose, lby, eye_yaw = get_entity_pose_data(ent)

            if sim_time > 0 then
                local r = resolver_db[ent]
                if not r then
                    r = {
                        last_sim = sim_time,
                        last_eye = eye_yaw,
                        deltas = {},
                        brute_stage = 0,
                        miss_count = 0,
                        lock_side = 0,
                        lock_until = 0,
                        last_applied_yaw = nil,
                        last_lby = lby,
                        lby_update_time = 0
                    }
                    resolver_db[ent] = r
                elseif sim_time > r.last_sim then
                    local d_eye = normalize_yaw(eye_yaw - r.last_eye)
                    table.insert(r.deltas, 1, d_eye)
                    if #r.deltas > 10 then table.remove(r.deltas) end

                    if lby ~= r.last_lby then
                        r.lby_update_time = cur_time + 1.1
                        r.last_lby = lby
                    end

                    r.last_eye = eye_yaw
                    r.last_sim = sim_time

                    local force_yaw = 0
                    local should_override = false
                    local mode_tag = "NATIVE"

                    if cur_time < r.lock_until then
                        force_yaw = r.lock_side
                        should_override = true
                        mode_tag = string_format("LOCKED (%d°)", force_yaw)
                    elseif r.miss_count > 0 then
                        local brute_angles = { 58, -58, 29, -29, 0, 15, -15 }
                        local stage_idx = (r.brute_stage % #brute_angles) + 1
                        force_yaw = brute_angles[stage_idx]
                        should_override = true
                        mode_tag = string_format("BRUTE [%d/7] (%d°)", stage_idx, force_yaw)
                    elseif cur_time < r.lby_update_time then
                        local lby_delta = normalize_yaw(eye_yaw - lby)
                        force_yaw = lby_delta ~= 0 and lby_delta or (body_yaw > 0 and 58 or -58)
                        should_override = true
                        mode_tag = string_format("LBY SYNC (%d°)", force_yaw)
                    elseif math_abs(body_yaw) > 22 then
                        local desync_side = body_yaw > 0 and 1 or -1
                        force_yaw = desync_side * math_min(58, math_max(28, math_floor(math_abs(body_yaw))))
                        should_override = true
                        mode_tag = string_format("POSE CORR (%d°)", force_yaw)
                    end

                    if should_override then
                        if r.last_applied_yaw ~= force_yaw or not state.jc_overridden_ents[ent] then
                            pcall(plist.set, ent, "Force body yaw", true)
                            pcall(plist.set, ent, "Force body yaw value", force_yaw)
                            r.last_applied_yaw = force_yaw
                            state.jc_overridden_ents[ent] = true
                        end
                    else
                        if state.jc_overridden_ents[ent] then
                            pcall(plist.set, ent, "Force body yaw", false)
                            r.last_applied_yaw = nil
                            state.jc_overridden_ents[ent] = nil
                        end
                    end

                    if ent == current_threat then
                        state.jc_currently_resolving = should_override
                        state.jc_active_mode_str = mode_tag
                        state.jc_active_target_desync = force_yaw
                        state.jc_active_target_name = entity.get_player_name(ent)
                    end
                end
            end
        else
            if state.jc_overridden_ents[ent] then
                pcall(plist.set, ent, "Force body yaw", false)
                state.jc_overridden_ents[ent] = nil
            end
        end
    end
end

local function reset_baim_overrides()
    for ent, _ in pairs(state.baim_overridden_ents) do
        pcall(plist.set, ent, "Override prefer body aim", "-")
    end
    for ent, _ in pairs(state.sp_overridden_ents) do
        pcall(plist.set, ent, "Override safe point", "-")
    end
    state.baim_overridden_ents = {}
    state.sp_overridden_ents = {}
    state.auto_baim_active = false
    rage_debug.baim_mode = "-"
    rage_debug.sp_mode = "-"
end

local function step_clean_position(ent, x, y, z, vx, vy, vz, on_ground, dt)
    if dt <= 0 or (vx == 0 and vy == 0 and vz == 0) then
        return x, y, z
    end
    local nx = x + vx * dt
    local ny = y + vy * dt
    local nz = z + (on_ground and 0 or (vz * dt - 0.5 * 800 * dt * dt))

    local frac = client.trace_line(ent, x, y, z, nx, ny, nz)
    if frac < 0.99 then
        local safe = math_max(0, frac - 0.08)
        nx = x + (nx - x) * safe
        ny = y + (ny - y) * safe
        nz = z + (nz - z) * safe
    end
    return nx, ny, nz
end

local primary_body_hitboxes = {2, 3, 4}

local function evaluate_combat_arbiter(me, current_threat, enemies, effective_mindmg, vx, vy, vz, speed2d, on_ground)
    local ex, ey, ez = client.eye_position()
    if not ex or not enemies or #enemies == 0 then
        reset_baim_overrides()
        return false, false, 0, 0
    end

    local tick_int = globals.tickinterval()
    local pred_on = ui_get(menu_refs.real_pred_enable)
    local pred_mode = ui_get(menu_refs.real_pred_mode)
    local pred_ticks = pred_on and get_effective_pred_ticks() or 2
    local ping_sec = math_min(0.12, (client.latency() or 0) * 0.5)

    local pred_local = pred_on and (pred_mode == "Full Sync (Me + Enemy)" or pred_mode == "Local Peek Only")
    local pred_enemy = pred_on and (pred_mode == "Full Sync (Me + Enemy)" or pred_mode == "Enemy Movement Only")

    local local_dt = (pred_ticks * tick_int) + (pred_local and ping_sec * 0.5 or 0)
    local is_moving = speed2d > 10

    local mid_ex, mid_ey, mid_ez = ex, ey, ez
    local end_ex, end_ey, end_ez = ex, ey, ez
    if is_moving and pred_local then
        mid_ex, mid_ey, mid_ez = step_clean_position(me, ex, ey, ez, vx, vy, vz, on_ground, local_dt * 0.5)
        end_ex, end_ey, end_ez = step_clean_position(me, ex, ey, ez, vx, vy, vz, on_ground, local_dt)
    end

    local baim_if_hidden = ui_get(menu_refs.auto_baim_peek)

    local threat_forced = false
    local threat_baim_str = "-"
    local threat_cur_hittable, threat_pred_hittable = false, false
    local best_cur_dmg, best_pred_dmg = 0, 0

    for i = 1, #enemies do
        local ent = enemies[i]
        local is_threat = (ent == current_threat)

        if entity_is_alive(ent) and not entity_is_dormant(ent) then
            local ox, oy, oz = entity.get_origin(ent)

            if is_threat or baim_if_hidden then
                local enemy_hp = entity_get_prop(ent, "m_iHealth") or 100
                local req_dmg = math_max(1, math_min(effective_mindmg, enemy_hp))

                local evx = entity_get_prop(ent, "m_vecVelocity[0]") or 0
                local evy = entity_get_prop(ent, "m_vecVelocity[1]") or 0
                local evz = entity_get_prop(ent, "m_vecVelocity[2]") or 0
                local e_speed = math_sqrt(evx * evx + evy * evy)
                local e_flags = entity_get_prop(ent, "m_fFlags") or 0
                local e_ground = bit.band(e_flags, 1) ~= 0

                local e_dx, e_dy, e_dz = 0, 0, 0
                if pred_enemy and ox then
                    local e_dt = (pred_ticks * tick_int) + ping_sec
                    local gravity_z = e_ground and 0 or (evz * e_dt - 0.5 * 800 * e_dt * e_dt)
                    local nx, ny, nz = step_clean_position(ent, ox, oy, oz, evx, evy, evz + gravity_z, e_ground, e_dt)
                    e_dx, e_dy, e_dz = nx - ox, ny - oy, nz - oz
                end

                local hx, hy, hz = entity.hitbox_position(ent, 0)
                local head_vis = false
                local cur_hd, pred_hd = 0, 0

                if hx then
                    local frac, hit_ent = client.trace_line(me, ex, ey, ez, hx, hy, hz)
                    head_vis = (hit_ent == ent) or (frac >= 0.96)
                    local _, hd1 = client.trace_bullet(me, ex, ey, ez, hx, hy, hz)
                    cur_hd = hd1 or 0
                    if is_threat and pred_on then
                        local _, hd_mid = client.trace_bullet(me, mid_ex, mid_ey, mid_ez, hx + e_dx * 0.5, hy + e_dy * 0.5, hz + e_dz * 0.5)
                        local _, hd_end = client.trace_bullet(me, end_ex, end_ey, end_ez, hx + e_dx, hy + e_dy, hz + e_dz)
                        pred_hd = math_max(hd_mid or 0, hd_end or 0)
                    else
                        pred_hd = cur_hd
                    end
                end

                local cur_bd_max, pred_bd_max = 0, 0
                local scan_hitboxes = {2, 3, 4, 5, 6}
                for j = 1, #scan_hitboxes do
                    local bx, by, bz = entity.hitbox_position(ent, scan_hitboxes[j])
                    if bx then
                        local _, bd1 = client.trace_bullet(me, ex, ey, ez, bx, by, bz)
                        if (bd1 or 0) > cur_bd_max then cur_bd_max = bd1 end
                        if is_threat and pred_on then
                            local _, bd_mid = client.trace_bullet(me, mid_ex, mid_ey, mid_ez, bx + e_dx * 0.5, by + e_dy * 0.5, bz + e_dz * 0.5)
                            local _, bd_end = client.trace_bullet(me, end_ex, end_ey, end_ez, bx + e_dx, hy + e_dy, bz + e_dz)
                            local best_p = math_max(bd_mid or 0, bd_end or 0)
                            if best_p > pred_bd_max then pred_bd_max = best_p end
                        end
                    end
                end

                if not (is_threat and pred_on) then
                    pred_bd_max = cur_bd_max
                end

                local body_ready_now = (cur_bd_max >= req_dmg)
                local body_ready_soon = (pred_bd_max >= req_dmg) or (cur_bd_max > 0 and cur_hd == 0)
                local final_baim = "-"

                if baim_if_hidden and not head_vis then
                    if body_ready_now then
                        final_baim = "Force"
                    elseif body_ready_soon then
                        final_baim = "High"
                    end
                end

                if final_baim ~= "-" then
                    pcall(plist.set, ent, "Override prefer body aim", final_baim)
                    state.baim_overridden_ents[ent] = true
                    if is_threat then
                        threat_forced = true
                        threat_baim_str = final_baim
                    end
                elseif state.baim_overridden_ents[ent] then
                    pcall(plist.set, ent, "Override prefer body aim", "-")
                    state.baim_overridden_ents[ent] = nil
                end

                if is_threat then
                    local ent_cur_best = math_max(cur_hd, cur_bd_max)
                    local ent_pred_best = math_max(pred_hd, pred_bd_max)

                    rage_debug.head_visible = head_vis
                    rage_debug.cur_head_dmg = cur_hd
                    rage_debug.cur_body_dmg = cur_bd_max
                    rage_debug.pred_head_dmg = pred_hd
                    rage_debug.pred_body_dmg = pred_bd_max
                    best_cur_dmg = ent_cur_best
                    best_pred_dmg = ent_pred_best

                    if ent_cur_best >= req_dmg then threat_cur_hittable = true end
                    if ent_pred_best >= req_dmg then threat_pred_hittable = true end
                end
            end
        else
            if state.baim_overridden_ents[ent] then
                pcall(plist.set, ent, "Override prefer body aim", "-")
                state.baim_overridden_ents[ent] = nil
            end
            if state.sp_overridden_ents[ent] then
                pcall(plist.set, ent, "Override safe point", "-")
                state.sp_overridden_ents[ent] = nil
            end
        end
    end

    state.auto_baim_active = threat_forced
    rage_debug.baim_mode = threat_baim_str
    rage_debug.pred_status = (threat_pred_hittable and not threat_cur_hittable) and string_format("PRE-FIRE (+%dt)", pred_ticks) or (threat_cur_hittable and "EXPOSED" or "WAIT")

    return threat_cur_hittable, threat_pred_hittable, best_cur_dmg, best_pred_dmg
end

local smg_ids = {[17]=true, [19]=true, [23]=true, [24]=true, [26]=true, [33]=true, [34]=true}
local shotgun_ids = {[25]=true, [27]=true, [29]=true, [35]=true}
local rifle_ids = {[7]=true, [8]=true, [10]=true, [13]=true, [16]=true, [39]=true, [60]=true}
local mg_ids = {[14]=true, [28]=true}

local function get_weapon_type(weapon)
    if not weapon then return nil end
    local classname = entity.get_classname(weapon)
    local idx = entity_get_prop(weapon, "m_iItemDefinitionIndex")
    if classname == "CWeaponSSG08" then return "SSG08" end
    if classname == "CWeaponAWP" then return "AWP" end
    if classname == "CWeaponSCAR20" or classname == "CWeaponG3SG1" then return "Auto snipers" end
    if idx == 1 then return "Desert eagle" end
    if idx == 64 then return "Revolver" end
    if smg_ids[idx] then return "SMG" end
    if shotgun_ids[idx] then return "Shotgun" end
    if rifle_ids[idx] then return "Rifles" end
    if mg_ids[idx] then return "Machinegun" end
    if string.find(classname or "", "Pistol") then return "Pistols" end
    return nil
end

local function get_weapon_group(weapon)
    if weapon == nil then return nil end
    local classname = entity.get_classname(weapon)
    local idx = entity_get_prop(weapon, "m_iItemDefinitionIndex")
    if classname == "CWeaponSSG08" then return "Scout" end
    if classname == "CWeaponAWP" then return "AWP" end
    if classname == "CWeaponSCAR20" or classname == "CWeaponG3SG1" then return "Auto Snipers" end
    if idx == 1 then return "Desert Eagle" end
    if idx == 64 then return "Revolver R8" end
    if string.find(classname or "", "Pistol") then return "Pistols" end
    return nil
end

local function execute_vector_autostop(cmd, vx, vy, speed2d, stop_threshold)
    if speed2d <= (stop_threshold or 20) then
        cmd.forwardmove = 0
        cmd.sidemove = 0
        return
    end
    local _, view_yaw = client.camera_angles()
    local vel_yaw = math_deg(math_atan2(vy, vx))
    local diff_rad = math_rad(normalize_yaw(view_yaw - vel_yaw))
    cmd.forwardmove = -math_cos(diff_rad) * 450
    cmd.sidemove = -math_sin(diff_rad) * 450
    if refs.quick_stop and refs.quick_stop[1] then ui_set(refs.quick_stop[1], true) end
end

local function set_early_stop(enable)
    rage_debug.early_qs_active = enable
    if not refs.quick_stop_options or not refs.quick_stop_options[1] then return end
    if enable then
        if not state.qs_forced_early then
            local current_opts = ui_get(refs.quick_stop_options[1]) or {}
            state.saved_qs_options = current_opts
            local has_early = false
            for _, opt in ipairs(current_opts) do
                if opt == "Early" then has_early = true break end
            end
            if not has_early then
                local new_opts = { unpack(current_opts) }
                table.insert(new_opts, "Early")
                ui_set(refs.quick_stop_options[1], new_opts)
                state.qs_forced_early = true
            end
        end
    else
        if state.qs_forced_early and state.saved_qs_options ~= nil then
            ui_set(refs.quick_stop_options[1], state.saved_qs_options)
            state.qs_forced_early = false
            state.saved_qs_options = nil
        end
    end
end

local function handle_force_shot_logic(cmd, me, threat, has_valid_threat, on_ground, wep_almost_ready, speed2d, cur_hittable, pred_hittable, base_hc, target_hc, hc_active)
    local fs_key_active = ui_get(menu_refs.force_shot_peek) and ui_get(menu_refs.force_shot_key)
    if not fs_key_active or not has_valid_threat then
        rage_debug.force_shot_state = "OFF"
        return target_hc, hc_active, "Native"
    end

    local is_quick_peeking = refs.quick_peek and refs.quick_peek[1] and ui_get(refs.quick_peek[1]) and ui_get(refs.quick_peek[2])
    local is_actively_peeking = is_quick_peeking or (speed2d > 35) or (not on_ground)

    local can_shoot_soon = pred_hittable or cur_hittable
    local new_hc = target_hc
    local is_active_hc = hc_active
    local reason = "ForcePeek"

    rage_debug.force_shot_state = "STANDBY"

    if is_actively_peeking and can_shoot_soon and wep_almost_ready then
        state.peek_fire_window_until = globals.tickcount() + 4
        rage_debug.force_shot_state = cur_hittable and "LETHAL PEEK" or "AIR / PRE-PEEK"

        local user_red = ui_get(menu_refs.force_shot_hc_red) or 12
        local min_safe_hc = 40
        local base_planned = hc_active and target_hc or base_hc
        
        new_hc = math_max(min_safe_hc, base_planned - user_red)
        is_active_hc = true
    end

    return new_hc, is_active_hc, reason
end

-- =========================================================================
-- ADVANCED 3D HITBOX & PREDICTION VISUALIZER
-- =========================================================================
local debug_hitboxes = {0, 2, 4, 6, 12}

local function draw_threat_prediction_debug(me, threat)
    if not threat or not entity_is_alive(threat) or entity_is_dormant(threat) then return end

    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local head_vis = rage_debug.head_visible
    local hr, hg, hb = head_vis and 135 or ar, head_vis and 255 or ag, head_vis and 140 or ab

    for i = 1, #debug_hitboxes do
        local hb_id = debug_hitboxes[i]
        local hx, hy, hz = entity.hitbox_position(threat, hb_id)
        if hx then
            local sx, sy = client.world_to_screen(hx, hy, hz)
            if sx and sy then
                local radius = (hb_id == 0) and 6 or 4
                renderer.rectangle(sx - radius, sy - radius, radius * 2, radius * 2, hr, hg, hb, 200)
                renderer.rectangle(sx - radius - 1, sy - radius - 1, radius * 2 + 2, radius * 2 + 2, 10, 10, 15, 120)
            end
        end
    end

    local pred_on = ui_get(menu_refs.real_pred_enable)
    if pred_on then
        local ox, oy, oz = entity.get_origin(threat)
        local evx = entity_get_prop(threat, "m_vecVelocity[0]") or 0
        local evy = entity_get_prop(threat, "m_vecVelocity[1]") or 0
        local evz = entity_get_prop(threat, "m_vecVelocity[2]") or 0
        
        if ox and (evx ~= 0 or evy ~= 0) then
            local tick_int = globals.tickinterval()
            local pred_ticks = get_effective_pred_ticks()
            local ping_sec = math_min(0.12, (client.latency() or 0) * 0.5)
            local total_dt = (pred_ticks * tick_int) + ping_sec

            local nx, ny, nz = step_clean_position(threat, ox, oy, oz, evx, evy, evz, false, total_dt)
            local px, py = client.world_to_screen(nx, ny, nz + 36)

            if px and py then
                renderer.circle_outline(px, py, 115, 220, 255, 240, 8, 0, 1, 2)
                renderer.circle_outline(px, py, 115, 220, 255, 100, 14, 0, 1, 1)
                renderer.text(px, py - 14, 115, 220, 255, 255, "c-d", 0, "PRED TARGET")
            end
        end
    end
end

-- =========================================================================
-- DT RECHARGE & TELEMETRY BAR RENDERER
-- =========================================================================
local function draw_dt_telemetry_bar(sizeX, sizeY)
    if not ui_get(menu_refs.vis_telemetry_enable) then return end
    local me = entity_get_local_player()
    if not me or not entity_is_alive(me) then return end

    local cx, cy = sizeX * 0.5, sizeY * 0.5 + 48
    local is_charged = antiaim_funcs.get_double_tap()
    
    state.dt_charge_smooth = lerp(state.dt_charge_smooth, is_charged and 1.0 or 0.0, 0.15)

    local bar_w = 110
    local bar_h = 4
    local bx = cx - (bar_w * 0.5)
    local by = cy

    renderer_rectangle(bx - 1, by - 1, bar_w + 2, bar_h + 2, 12, 12, 16, 200)
    renderer_rectangle(bx, by, bar_w, bar_h, 25, 25, 32, 220)

    local filled_w = math_floor(bar_w * state.dt_charge_smooth)
    if filled_w > 0 then
        local r, g, b = is_charged and 135 or 255, is_charged and 255 or 180, is_charged and 140 or 80
        renderer_gradient(bx, by, filled_w, bar_h, r, g, b, 255, r - 30, g - 30, b - 30, 255, true)
    end

    local status_str = is_charged and "DT: READY" or "DT: RECHARGING"
    local sr, sg, sb = is_charged and 135 or 255, is_charged and 255 or 140, is_charged and 140 or 90
    renderer_text(cx, by - 12, sr, sg, sb, 255, "c-d", 0, status_str)
end

-- =========================================================================
-- EVENTS & CALLBACKS (STATS & LOGS)
-- =========================================================================
local function push_log(str, r, g, b)
    client.color_log(r, g, b, "[SEGFAULT] " .. str)
    table.insert(state.log_notifications, { time = globals.curtime(), string = str, color = {r, g, b, 255}, fraction = 0 })
    if #state.log_notifications > 6 then table.remove(state.log_notifications, 1) end
end

client.set_event_callback("aim_miss", function(e)
    if not ui_get(menu_refs.master_switch) then return end
    local target = e.target
    local reason = e.reason or "unknown"

    round_stats.shots_fired = round_stats.shots_fired + 1

    if reason == "resolver" and target and resolver_db[target] then
        local r = resolver_db[target]
        r.miss_count = r.miss_count + 1
        r.brute_stage = (r.brute_stage + 1) % 7
        r.lock_until = 0
        client.color_log(255, 140, 0, string_format("[SEGFAULT] Resolver miss on %s. Auto-Brute stage -> %d", entity.get_player_name(target) or "target", r.brute_stage))
    end

    if ui_get(menu_refs.vis_logs_enable) then
        local group = hitgroup_names[e.hitgroup + 1] or '?'
        local target_name = entity.get_player_name(target) or "enemy"
        push_log(string_format("Missed %s's %s due to %s", target_name, string_lower(group), reason), 255, 100, 100)
    end
end)

client.set_event_callback("aim_hit", function(e)
    if not ui_get(menu_refs.master_switch) then return end
    local target = e.target

    round_stats.shots_fired = round_stats.shots_fired + 1
    round_stats.shots_hit = round_stats.shots_hit + 1
    round_stats.total_damage = round_stats.total_damage + e.damage

    local hg_name = hitgroup_names[e.hitgroup + 1] or 'Generic'
    round_stats.hitgroups[hg_name] = (round_stats.hitgroups[hg_name] or 0) + 1

    if target and resolver_db[target] then
        local r = resolver_db[target]
        if r.last_applied_yaw then
            r.lock_side = r.last_applied_yaw
            r.lock_until = globals.curtime() + 1.5
        end
        r.miss_count = 0
        r.brute_stage = 0
    end

    if ui_get(menu_refs.vis_logs_enable) then
        local target_name = entity.get_player_name(target) or "enemy"
        local target_hp = entity_get_prop(target, "m_iHealth") or 0
        local r, g, b = ui_get(menu_refs.vis_logs_color)
        push_log(string_format("Hit %s in %s for %d dmg (%d HP left)", target_name, string_lower(hg_name), e.damage, target_hp), r, g, b)
    end
end)

client.set_event_callback("player_hurt", function(e)
    if not ui_get(menu_refs.master_switch) then return end
    local me = entity_get_local_player()
    if me == nil or client.userid_to_entindex(e.attacker) ~= me then return end

    if ui_get(menu_refs.hm_enable) then
        state.hitmarker_alpha = 255
        state.hitmarker_time = globals.curtime() + (ui_get(menu_refs.hm_duration) * 0.01)
    end

    if ui_get(menu_refs.tesla_enable) and fs_tesla ~= nil then
        local hurt = client.userid_to_entindex(e.userid)
        local r, g, b = ui_get(menu_refs.tesla_color)
        local x = client.random_float(-1000, 1000)
        local y = client.random_float(-x, x)
        local z = client.random_float(-y, y)
        local tesla_info = ffi.new("struct tesla_info_t_sfg")
        tesla_info.m_flbeamwidth = ui_get(menu_refs.tesla_width)
        tesla_info.m_flradius = ui_get(menu_refs.tesla_radius)
        tesla_info.m_entindex = me
        tesla_info.m_color = {r / 255, g / 255, b / 255}
        tesla_info.m_pos = { entity.hitbox_position(hurt, 6) }
        tesla_info.m_ang = {x, y, z}
        tesla_info.m_fltimevis = 0.75
        tesla_info.m_nbeams = ui_get(menu_refs.tesla_beams)
        tesla_info.m_spritename = "sprites/physbeam.vmt"
        fs_tesla(tesla_info)
    end
end)

client.set_event_callback("aim_fire", function()
    if not ui_get(menu_refs.master_switch) then return end
    state.last_shot_tick = globals.tickcount()
    state.land_stop_until = 0
end)

local function dump_round_stats()
    if round_stats.shots_fired == 0 then return end
    local acc = math_floor((round_stats.shots_hit / round_stats.shots_fired) * 100 + 0.5)
    client.color_log(150, 200, 255, "================ [SEGFAULT ROUND STATS] ================")
    client.color_log(235, 235, 245, string_format(" Shots Fired: %d | Hits: %d | Accuracy: %d%% | Total DMG: %d", round_stats.shots_fired, round_stats.shots_hit, acc, round_stats.total_damage))
    for hg, count in pairs(round_stats.hitgroups) do
        if count > 0 then
            client.color_log(180, 220, 180, string_format(" -> %s: %d hits", hg, count))
        end
    end
    client.color_log(150, 200, 255, "========================================================")
    reset_round_stats()
end

local function reset_round_state()
    dump_round_stats()
    state.hp_players = {}
    state.was_in_air = false
    state.land_stop_until = 0
    state.defensive_records = {}
    set_early_stop(false)
    reset_baim_overrides()
    reset_entity_resolver()
end

client.set_event_callback("round_start", function()
    reset_round_stats()
end)
client.set_event_callback("round_end", reset_round_state)

-- =========================================================================
-- UNIFIED SETUP_COMMAND
-- =========================================================================
client.set_event_callback("setup_command", function(cmd)
    if not ui_get(menu_refs.master_switch) then
        reset_baim_overrides()
        reset_entity_resolver()
        return
    end
    local me = entity_get_local_player()
    if me == nil or not entity_is_alive(me) then
        reset_baim_overrides()
        reset_entity_resolver()
        return
    end

    local weapon = entity.get_player_weapon(me)

    if ui_get(menu_refs.vis_vm_enable) and weapon ~= nil then
        local classname = entity.get_classname(weapon)
        local mode = (classname == "CKnife") and ui_get(menu_refs.vis_hand_knife) or ui_get(menu_refs.vis_hand_weapon)
        if state.last_hand ~= mode then
            client.exec(mode == "Left" and "cl_righthand 0" or "cl_righthand 1")
            state.last_hand = mode
        end
    end

    if ui_get(menu_refs.misc_ladder) then
        local throw = entity_get_prop(me, "m_fThrowTime")
        if entity_get_prop(me, "m_MoveType") == 9 and (throw == nil or throw == 0) then
            local forward = vector(entity_get_prop(me, "m_vecLadderNormal"))
            if forward:lengthsqr() ~= 0 then
                local view = vector(client.camera_angles())
                local angle = vector(forward:angles())
                local delta_yaw = normalize_yaw(angle.y - view.y + 180)
                local delta_pitch = math_max(-89, math_min(89, angle.x - view.x))
                local abs_yaw = math_abs(delta_yaw)
                local pitch, yaw_offset = 89, -90
                local is_looking_down = delta_pitch < -45
                local is_looking_to_right = delta_yaw > 0
                local is_sidemove, is_forwardmove = cmd.sidemove > 0, cmd.forwardmove > 0

                if abs_yaw > 70 and abs_yaw < 135 then
                    if cmd.forwardmove == 0 and cmd.sidemove ~= 0 then
                        if not is_looking_to_right then yaw_offset = -yaw_offset end
                        if is_looking_to_right then is_sidemove = not is_sidemove end
                        cmd.in_back, cmd.in_forward = is_sidemove and 1 or 0, is_sidemove and 0 or 1
                        if is_looking_to_right then is_sidemove = not is_sidemove end
                        cmd.in_moveleft, cmd.in_moveright = is_sidemove and 1 or 0, is_sidemove and 0 or 1
                        cmd.pitch, cmd.yaw = pitch, normalize_yaw(angle.y + yaw_offset)
                    end
                elseif cmd.sidemove == 0 and cmd.forwardmove ~= 0 then
                    if not is_looking_to_right then yaw_offset = -yaw_offset end
                    if not is_looking_down then is_forwardmove = not is_forwardmove end
                    cmd.in_back, cmd.in_forward = is_forwardmove and 0 or 1, is_forwardmove and 1 or 0
                    if not is_looking_to_right then is_forwardmove = not is_forwardmove end
                    cmd.in_moveleft, cmd.in_moveright = is_forwardmove and 1 or 0, is_forwardmove and 0 or 1
                    cmd.pitch, cmd.yaw = pitch, normalize_yaw(angle.y + yaw_offset)
                end
            end
        end
    end

    local flags = entity_get_prop(me, "m_fFlags") or 0
    local on_ground = bit.band(flags, 1) ~= 0
    local w_type = get_weapon_type(weapon)
    local w_group = get_weapon_group(weapon)
    local curtime = globals.curtime()
    local next_atk = entity_get_prop(me, "m_flNextAttack") or 0
    local next_prim = weapon and (entity_get_prop(weapon, "m_flNextPrimaryAttack") or 0) or 0
    local wep_ready = weapon ~= nil and (curtime >= next_atk) and (curtime >= next_prim)
    local wep_almost_ready = weapon ~= nil and (curtime + 0.08 >= next_atk) and (curtime + 0.08 >= next_prim)

    local threat = client.current_threat()
    local has_valid_threat = threat ~= nil and entity_is_alive(threat) and not entity_is_dormant(threat)
    local threat_dist = 9999
    if has_valid_threat then
        local mx, my, mz = entity.get_origin(me)
        local tx, ty, tz = entity.get_origin(threat)
        if mx and tx then
            local dx, dy, dz = tx - mx, ty - my, tz - mz
            threat_dist = math_sqrt(dx * dx + dy * dy + dz * dz)
        end
    end

    local enemies = entity_get_players(true)
    local vx = entity_get_prop(me, "m_vecVelocity[0]") or 0
    local vy = entity_get_prop(me, "m_vecVelocity[1]") or 0
    local vz = entity_get_prop(me, "m_vecVelocity[2]") or 0
    local speed2d = math_sqrt(vx * vx + vy * vy)
    local tickcount = globals.tickcount()
    local tick_int = globals.tickinterval()

    if speed2d > 28 then state.last_move_tick = tickcount end

    rage_debug.weapon_name = w_type or (weapon and entity.get_classname(weapon) or "None")
    rage_debug.weapon_ready = wep_ready
    rage_debug.my_speed = math_floor(speed2d)
    rage_debug.threat_ent = has_valid_threat and threat or nil

    if has_valid_threat then
        rage_debug.threat_name = entity.get_player_name(threat) or "Enemy"
        rage_debug.threat_hp = entity_get_prop(threat, "m_iHealth") or 0
        rage_debug.threat_dist = math_floor(threat_dist)
        local tvx = entity_get_prop(threat, "m_vecVelocity[0]") or 0
        local tvy = entity_get_prop(threat, "m_vecVelocity[1]") or 0
        rage_debug.threat_speed = math_floor(math_sqrt(tvx * tvx + tvy * tvy))
    else
        rage_debug.threat_name = "None"
        rage_debug.threat_hp = 0
        rage_debug.threat_dist = 0
        rage_debug.threat_speed = 0
        rage_debug.threat_state = "None"
        rage_debug.head_visible = false
        rage_debug.cur_head_dmg = 0
        rage_debug.cur_body_dmg = 0
        rage_debug.pred_head_dmg = 0
        rage_debug.pred_body_dmg = 0
        rage_debug.pred_status = "IDLE"
    end

    local is_peeking = refs.quick_peek and ui_get(refs.quick_peek[1]) and ui_get(refs.quick_peek[2])

    run_functional_jitter_resolver(me, threat, enemies)

    local is_def_threat = false
    local def_choked = 0

    if has_valid_threat then
        is_def_threat, def_choked = update_defensive_tracker(threat, tickcount, tick_int)

        if is_def_threat then
            rage_debug.threat_state = string_format("DEFENSIVE (%dt)", def_choked)
            if refs.sp and refs.sp[1] then
                ui_set(refs.sp[1], true)
            end
            pcall(plist.set, threat, "Override prefer body aim", "Force")
            state.baim_overridden_ents[threat] = true
        elseif state.jc_currently_resolving then
            rage_debug.threat_state = "JC: " .. state.jc_active_mode_str
        else
            rage_debug.threat_state = "Normal"
        end
    end

    local dt_trigger_active = false
    if ui_get(menu_refs.dt_fix_enable) and has_valid_threat then
        local dt_mode = ui_get(menu_refs.dt_fix_weapons)
        local is_auto = (w_type == "Auto snipers")
        local is_valid_weapon = (dt_mode == "Auto Snipers Only" and is_auto) or (dt_mode == "All Snipers" and (is_auto or w_type == "SSG08" or w_type == "AWP"))
        if is_valid_weapon and rage_debug.threat_speed >= ui_get(menu_refs.dt_fix_speed) then
            local mx, my = entity.get_origin(me)
            local tx, ty = entity.get_origin(threat)
            if mx and tx then
                local dir_x, dir_y = mx - tx, my - ty
                local dir_len = math_sqrt(dir_x * dir_x + dir_y * dir_y)
                if dir_len > 0 then
                    local tvx = entity_get_prop(threat, "m_vecVelocity[0]") or 0
                    local tvy = entity_get_prop(threat, "m_vecVelocity[1]") or 0
                    local dot = ((tvx / rage_debug.threat_speed) * (dir_x / dir_len)) + ((tvy / rage_debug.threat_speed) * (dir_y / dir_len))
                    dt_trigger_active = dot > 0.25
                end
            end
        end
    end
    rage_debug.dt_fix_active = dt_trigger_active

    if dt_trigger_active then
        if not state.dt_fix_applied then
            if refs.sp and refs.sp[1] then state.dt_saved_sp = ui_get(refs.sp[1]) end
            state.dt_fix_applied = true
        end
        if refs.sp and refs.sp[1] then ui_set(refs.sp[1], true) end
    elseif state.dt_fix_applied and not is_def_threat then
        if state.dt_saved_sp ~= nil and refs.sp and refs.sp[1] then
            ui_set(refs.sp[1], state.dt_saved_sp)
            state.dt_saved_sp = nil
        end
        state.dt_fix_applied = false
    end

    local base_hc = (state.hc_cache ~= nil) and state.hc_cache or (refs.hitchance and refs.hitchance[1] and ui_get(refs.hitchance[1]) or 50)
    local base_dmg = (state.mindmg_cache ~= nil) and state.mindmg_cache or (refs.mindmg and refs.mindmg[1] and ui_get(refs.mindmg[1]) or 20)

    local hc_active = false
    local target_hc = base_hc
    local hc_reason = "Native"
    local target_dmg = nil
    local dmg_reason = "Native"

    if ui_get(menu_refs.mindmg_boost_enable) and enemies ~= nil then
        local threshold = ui_get(menu_refs.mindmg_hp_threshold)
        for i = 1, #enemies do
            local ent = enemies[i]
            if entity_is_alive(ent) and not entity_is_dormant(ent) then
                if (entity_get_prop(ent, "m_iHealth") or 100) <= threshold then
                    target_dmg = 1
                    dmg_reason = "Lethal HP"
                    break
                end
            end
        end
    end

    if dt_trigger_active then
        hc_active = true
        target_hc = ui_get(menu_refs.dt_fix_hc)
        hc_reason = "DT Peek"
    elseif ui_get(menu_refs.hc_enable) and w_group and hc_settings[w_group] then
        local s = hc_settings[w_group]
        local active_opts = ui_get(s.options)
        local function has_opt(opt)
            for i = 1, #active_opts do if active_opts[i] == opt then return true end end
            return false
        end

        if has_opt("Hotkey") and ui_get(menu_refs.hc_hotkey) then
            hc_active, target_hc, hc_reason = true, ui_get(s["Hotkey"].val), "Hotkey"
        elseif has_opt("Peek Assist") and is_peeking then
            hc_active, target_hc, hc_reason = true, ui_get(s["Peek Assist"].val), "Peek Assist"
        elseif has_opt("In Air") and not on_ground then
            hc_active, target_hc, hc_reason = true, ui_get(s["In Air"].val), "In Air"
            if s["In Air"].dmg then
                local custom_air_dmg = ui_get(s["In Air"].dmg)
                if custom_air_dmg > 0 then target_dmg, dmg_reason = custom_air_dmg, "In Air" end
            end
        elseif has_opt("Crouch") and (entity_get_prop(me, "m_flDuckAmount") or 0) > 0.5 then
            hc_active, target_hc, hc_reason = true, ui_get(s["Crouch"].val), "Crouch"
        elseif has_opt("No Scope") and entity_get_prop(me, "m_bIsScoped") == 0 then
            local max_dist = ui_get(s["No Scope"].dist)
            if max_dist == 101 or (threat_dist * 0.025) <= max_dist then
                hc_active, target_hc, hc_reason = true, ui_get(s["No Scope"].val), "No Scope"
            end
        end
    end

    local planned_dmg = target_dmg or base_dmg
    local cur_hittable, pred_hittable, best_cur_dmg, best_pred_dmg = evaluate_combat_arbiter(me, threat, enemies, planned_dmg, vx, vy, vz, speed2d, on_ground)

    local active_autostop_weapons = ui_get(menu_refs.on_land_weapons) or {}
    local is_autostop_wep = false
    if w_type then
        for i = 1, #active_autostop_weapons do
            if active_autostop_weapons[i] == w_type then is_autostop_wep = true break end
        end
    end

    if ui_get(menu_refs.on_land_enable) and is_autostop_wep then
        local land_mode = ui_get(menu_refs.on_land_mode)
        local target_exposed = (land_mode == "Smart (Only if target hittable)")
            and (cur_hittable or pred_hittable or best_cur_dmg > 0 or best_pred_dmg > 0 or rage_debug.head_visible)
            or (has_valid_threat and cmd.in_jump == 0)

        if state.was_in_air and on_ground and has_valid_threat and target_exposed and wep_almost_ready then
            state.land_stop_until = tickcount + 5
        end

        if state.land_stop_until > tickcount and on_ground then
            if speed2d > 26 and (tickcount - state.last_shot_tick) > 2 then
                execute_vector_autostop(cmd, vx, vy, speed2d, 22)
            else
                state.land_stop_until = 0
            end
        end
    else
        state.land_stop_until = 0
    end

    if ui_get(menu_refs.in_air_stop) and not on_ground and has_valid_threat and wep_ready then
        local max_air_dist = ui_get(menu_refs.in_air_dist)
        local air_target_exposed = (cur_hittable or pred_hittable or best_cur_dmg >= (planned_dmg * 0.7))
        if (max_air_dist == 1001 or threat_dist <= max_air_dist) and air_target_exposed then
            if vz <= 75 and speed2d > 20 then
                execute_vector_autostop(cmd, vx, vy, speed2d, 15)
            end
        end
    end

    state.was_in_air = not on_ground

    local want_early_qs = (ui_get(menu_refs.early_stop_def) and is_def_threat) or false
    target_hc, hc_active, hc_reason = handle_force_shot_logic(cmd, me, threat, has_valid_threat, on_ground, wep_almost_ready, speed2d, cur_hittable, pred_hittable, base_hc, target_hc, hc_active)

    if ui_get(menu_refs.real_pred_enable) and on_ground and has_valid_threat and pred_hittable and speed2d > 45 then
        want_early_qs = true
    end

    set_early_stop(want_early_qs)

    if refs.hitchance ~= nil and refs.hitchance[1] ~= nil then
        if hc_active then
            if state.hc_cache == nil then state.hc_cache = ui_get(refs.hitchance[1]) end
            ui_set(refs.hitchance[1], target_hc)
        elseif state.hc_cache ~= nil then
            ui_set(refs.hitchance[1], state.hc_cache)
            state.hc_cache = nil
        end
    end

    if refs.mindmg ~= nil and refs.mindmg[1] ~= nil then
        if target_dmg ~= nil then
            if state.mindmg_cache == nil then state.mindmg_cache = ui_get(refs.mindmg[1]) end
            ui_set(refs.mindmg[1], target_dmg)
        elseif state.mindmg_cache ~= nil then
            ui_set(refs.mindmg[1], state.mindmg_cache)
            state.mindmg_cache = nil
        end
    end

    local final_hc = hc_active and target_hc or base_hc
    local final_dmg = target_dmg or base_dmg

    rage_debug.base_hc, rage_debug.active_hc, rage_debug.hc_reason = base_hc, final_hc, hc_reason
    rage_debug.base_dmg, rage_debug.active_dmg, rage_debug.dmg_reason = base_dmg, final_dmg, dmg_reason

    if not has_valid_threat then
        rage_debug.blocker_text, rage_debug.short_status, rage_debug.blocker_color = "no target", "IDLE", {160, 160, 170}
    elseif not wep_ready then
        rage_debug.blocker_text, rage_debug.short_status, rage_debug.blocker_color = "weapon cooldown / reload", "WAIT CD", {255, 180, 80}
    else
        local req_dmg = math_min(final_dmg, rage_debug.threat_hp > 0 and rage_debug.threat_hp or 100)
        if best_cur_dmg < req_dmg then
            if best_pred_dmg >= req_dmg then
                rage_debug.blocker_text = string_format("peek pred ready (%d >= %d dmg)", best_pred_dmg, req_dmg)
                rage_debug.short_status, rage_debug.blocker_color = "PRE-FIRE", {100, 220, 255}
            elseif best_cur_dmg > 0 then
                rage_debug.blocker_text = string_format("dmg < mindmg (%d < %d)", best_cur_dmg, req_dmg)
                rage_debug.short_status, rage_debug.blocker_color = "LOW DMG", {255, 95, 95}
            else
                rage_debug.blocker_text, rage_debug.short_status, rage_debug.blocker_color = "behind wall (0 dmg)", "COVER", {175, 175, 185}
            end
        elseif speed2d > 85 and on_ground then
            rage_debug.blocker_text = string_format("stopping for hc (spd: %d)", math_floor(speed2d))
            rage_debug.short_status, rage_debug.blocker_color = "STOPPING", {255, 220, 90}
        else
            rage_debug.blocker_text = string_format("ready to fire (%d dmg)", best_cur_dmg)
            rage_debug.short_status, rage_debug.blocker_color = "FIRE!", {130, 255, 135}
        end
    end
end)

-- =========================================================================
-- CUSTOM 2x3 INTERACTIVE WEAPON GRID CARDS RENDERER (DYNAMIC MENU POSITION)
-- =========================================================================
local weapon_grid_cards = {
    { name = "Auto Snipers", title = "Auto Sniper", icon = "d" },
    { name = "Scout",        title = "Scout",       icon = "c" },
    { name = "AWP",          title = "AWP",         icon = "r" },
    { name = "Desert Eagle", title = "Desert Eagle",icon = "a" },
    { name = "Revolver R8",  title = "Revolver R8", icon = "b" },
    { name = "Pistols",      title = "Pistols",     icon = "p" }
}

local function draw_custom_weapon_grid(sizeX, sizeY)
    if not ui.is_menu_open() then return end
    if not ui_get(menu_refs.master_switch) then return end
    if ui_get(menu_refs.tab_selector) ~= "🎯 Aim Tools" then return end
    if not ui_get(menu_refs.hc_enable) then return end

    local menu_x, menu_y = ui.menu_position()
    if not menu_x or not menu_y then return end

    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local selected_wep = ui_get(menu_refs.hc_weapon)

    local start_x = menu_x + 310
    local start_y = menu_y + 45
    local card_w = 145
    local card_h = 52
    local gap_x = 8
    local gap_y = 8

    local mx, my = ui.mouse_position()
    local left_down = client.key_state(0x01)
    local mouse_clicked = left_down and not state.last_mouse_down
    state.last_mouse_down = left_down

    renderer_text(start_x, start_y - 20, 220, 220, 230, 255, "b", 0, "WEAPON ARSENAL PROFILES")
    renderer_rectangle(start_x, start_y - 4, (card_w * 3) + (gap_x * 2), 1, 60, 60, 70, 200)

    for i = 1, #weapon_grid_cards do
        local item = weapon_grid_cards[i]
        local row = math_floor((i - 1) / 3)
        local col = (i - 1) % 3

        local x = start_x + (col * (card_w + gap_x))
        local y = start_y + (row * (card_h + gap_y))

        local hovered = (mx >= x and mx <= x + card_w and my >= y and my <= y + card_h)
        local is_active = (selected_wep == item.name)

        if hovered and mouse_clicked then
            ui_set(menu_refs.hc_weapon, item.name)
            selected_wep = item.name
            is_active = true
        end

        local bg_a = is_active and 220 or (hovered and 170 or 120)
        renderer_rectangle(x, y, card_w, card_h, 18, 18, 22, bg_a)

        if is_active then
            renderer_rectangle(x, y, card_w, 2, ar, ag, ab, 255)
            renderer_rectangle(x, y + card_h - 1, card_w, 1, ar, ag, ab, 180)
            renderer_rectangle(x, y, 1, card_h, ar, ag, ab, 180)
            renderer_rectangle(x + card_w - 1, y, 1, card_h, ar, ag, ab, 180)
        else
            local outline_c = hovered and 80 or 40
            renderer_rectangle(x, y, card_w, 1, outline_c, outline_c, outline_c + 10, 200)
            renderer_rectangle(x, y + card_h - 1, card_w, 1, outline_c, outline_c + 10, 200)
            renderer_rectangle(x, y, 1, card_h, outline_c, outline_c + 10, 200)
            renderer_rectangle(x + card_w - 1, y, 1, card_h, outline_c, outline_c + 10, 200)
        end

        local title_r, title_g, title_b = is_active and 255 or (hovered and 220 or 160), is_active and 255 or (hovered and 220 or 160), is_active and 255 or (hovered and 220 or 170)
        renderer_text(x + 10, y + 8, title_r, title_g, title_b, 255, "b", 0, item.title)

        if is_active then
            renderer_text(x + card_w - 18, y + 6, ar, ag, ab, 255, "b", 0, "✓")
        end

        local w_hc = (refs.hitchance and refs.hitchance[1] and ui_get(refs.hitchance[1])) or 50
        local w_dmg = (refs.mindmg and refs.mindmg[1] and ui_get(refs.mindmg[1])) or 20

        local s = hc_settings[item.name]
        if s then
            if s["In Air"] and s["In Air"].dmg then
                local air_dmg = ui_get(s["In Air"].dmg)
                if air_dmg and air_dmg > 0 then w_dmg = air_dmg end
            end
            if s["Hotkey"] and s["Hotkey"].val then
                local ovr_hc = ui_get(s["Hotkey"].val)
                if ovr_hc and ovr_hc > 0 then w_hc = ovr_hc end
            end
        end

        local stat_str = string_format("HC: %d%%  |  DMG: %d", w_hc, w_dmg)
        local stat_r, stat_g, stat_b = is_active and ar or 140, is_active and ag or 140, is_active and ab or 150
        renderer_text(x + 10, y + 36, stat_r, stat_g, stat_b, 255, "-", 0, stat_str)
    end
end

-- =========================================================================
-- MOUSE DRAGGABLE 8-STYLE RAGE DEBUG RENDERER
-- =========================================================================
local function handle_debug_panel_dragging(sizeX, sizeY, style)
    if style == "Skeet Indicators" or style == "Crosshair Sub-Text" then
        state.is_dragging = false
        return ui_get(menu_refs.debug_panel_x), ui_get(menu_refs.debug_panel_y)
    end

    local x = ui_get(menu_refs.debug_panel_x)
    local y = ui_get(menu_refs.debug_panel_y)

    if not ui.is_menu_open() then
        state.is_dragging = false
        return x, y
    end

    local mx, my = ui.mouse_position()
    local left_down = client.key_state(0x01)
    local w, h = state.panel_w, state.panel_h

    local hovered = (mx >= x - 4 and mx <= x + w + 4 and my >= y - 4 and my <= y + h + 4)

    if left_down then
        if not state.is_dragging and hovered then
            state.is_dragging = true
            state.drag_offset_x = mx - x
            state.drag_offset_y = my - y
        end
        if state.is_dragging then
            x = math_max(4, math_min(sizeX - w - 4, mx - state.drag_offset_x))
            y = math_max(4, math_min(sizeY - h - 4, my - state.drag_offset_y))
            ui_set(menu_refs.debug_panel_x, x)
            ui_set(menu_refs.debug_panel_y, y)
        end
    else
        state.is_dragging = false
    end

    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local box_alpha = (state.is_dragging or hovered) and 200 or 85
    renderer_rectangle(x - 4, y - 16, w + 8, h + 20, 15, 15, 20, (state.is_dragging or hovered) and 90 or 35)
    renderer_rectangle(x - 4, y - 16, w + 8, 1, ar, ag, ab, box_alpha)
    renderer_text(x, y - 14, ar, ag, ab, box_alpha, "-", 0, state.is_dragging and "DRAGGING PANEL..." or "DRAG WITH MOUSE")

    return x, y
end

local function draw_rage_debug_panel(sizeX, sizeY, scopedFraction)
    if not ui_get(menu_refs.debug_panel_enable) then return end
    local me = entity_get_local_player()
    if not me or not entity_is_alive(me) then return end

    local style = ui_get(menu_refs.debug_panel_style)
    local x, y = handle_debug_panel_dragging(sizeX, sizeY, style)
    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local bc = rage_debug.blocker_color

    local c_acc   = hex_color(ar, ag, ab, 255)
    local c_white = hex_color(235, 235, 240, 255)
    local c_gray  = hex_color(155, 155, 165, 255)
    local c_stat  = hex_color(bc[1], bc[2], bc[3], 255)
    local c_green = hex_color(135, 255, 140, 255)
    local c_cyan  = hex_color(115, 220, 255, 255)

    local hc_col   = (rage_debug.active_hc ~= rage_debug.base_hc) and c_cyan or c_white
    local dmg_col  = (rage_debug.active_dmg ~= rage_debug.base_dmg) and c_green or c_white
    local baim_col = (rage_debug.baim_mode ~= "-") and c_green or c_gray

    if style == "Clean Side Text" then
        state.panel_w, state.panel_h = 275, 98
        local lines = {
            c_acc .. "segfault" .. c_gray .. ".rage_debug [" .. c_white .. rage_debug.weapon_name .. c_gray .. "]",
            c_gray .. "├─ state: " .. c_stat .. rage_debug.blocker_text,
            string_format("%s├─ target: %s%s %s(%d hp | %s)", c_gray, c_white, string_lower(rage_debug.threat_name), c_gray, rage_debug.threat_hp, string_lower(rage_debug.threat_state)),
            string_format("%s├─ hitchance: %s%d%% -> %d%% %s[%s]", c_gray, hc_col, rage_debug.base_hc, rage_debug.active_hc, c_gray, string_lower(rage_debug.hc_reason)),
            string_format("%s├─ min-dmg: %s%d -> %d %s[%s]", c_gray, dmg_col, rage_debug.base_dmg, rage_debug.active_dmg, c_gray, string_lower(rage_debug.dmg_reason)),
            string_format("%s├─ pred: %s%s %s| dmg: %sh:%d b:%d %s(cur: %sh:%d b:%d%s)",
                c_gray, c_cyan, string_lower(rage_debug.pred_status), c_gray,
                c_cyan, rage_debug.pred_head_dmg, rage_debug.pred_body_dmg,
                c_gray, c_white, rage_debug.cur_head_dmg, rage_debug.cur_body_dmg, c_gray),
            string_format("%s└─ arbiter: %sbaim:%s%s", c_gray, c_gray, baim_col, string_lower(rage_debug.baim_mode))
        }
        for i = 1, #lines do renderer_text(x, y + (i - 1) * 14, 255, 255, 255, 255, "d", 0, lines[i]) end

    elseif style == "Minimal Pixel (-)" then
        state.panel_w, state.panel_h = 245, 50
        local lines = {
            c_acc .. "SFG // " .. c_stat .. string_upper(rage_debug.blocker_text),
            string_format("%sTGT: %s%s (%dHP) %s| %s", c_gray, c_white, string_upper(rage_debug.threat_name), rage_debug.threat_hp, c_gray, string_upper(rage_debug.threat_state)),
            string_format("%sHC: %s%d->%d%% (%s) %s| DMG: %s%d->%d (%s)", c_gray, hc_col, rage_debug.base_hc, rage_debug.active_hc, string_upper(rage_debug.hc_reason), c_gray, dmg_col, rage_debug.base_dmg, rage_debug.active_dmg, string_upper(rage_debug.dmg_reason)),
            string_format("%sPRED: %s%s (B:%d) %s| BAIM:%s%s", c_gray, c_cyan, rage_debug.pred_status, rage_debug.pred_body_dmg, c_gray, baim_col, string_upper(rage_debug.baim_mode))
        }
        for i = 1, #lines do renderer_text(x, y + (i - 1) * 10, 255, 255, 255, 255, "-", 0, lines[i]) end

    elseif style == "Skeet Indicators" then
        renderer_indicator(bc[1], bc[2], bc[3], 255, "RAGE: " .. rage_debug.short_status)
        if rage_debug.baim_mode ~= "-" then
            renderer_indicator(135, 255, 140, 255, string_format("BAIM:%s", rage_debug.baim_mode))
        end

    elseif style == "Compact Gradient" then
        state.panel_w, state.panel_h = 240, 62
        renderer_gradient(x, y, 240, 62, 10, 10, 14, 155, 10, 10, 14, 0, true)
        renderer_gradient(x, y, 2, 62, ar, ag, ab, 255, bc[1], bc[2], bc[3], 255, false)
        renderer_text(x + 8, y + 4, 255, 255, 255, 255, "d", 0, c_acc .. "SEGFAULT " .. c_gray .. "// " .. c_stat .. rage_debug.blocker_text)
        renderer_text(x + 8, y + 18, 255, 255, 255, 255, "d", 0, string_format("%sHC: %s%d%% %s| DMG: %s%d %s| BAIM: %s%s", c_gray, hc_col, rage_debug.active_hc, c_gray, dmg_col, rage_debug.active_dmg, c_gray, baim_col, rage_debug.baim_mode))
        renderer_text(x + 8, y + 32, 255, 255, 255, 255, "d", 0, string_format("%sPred: %s%s %s(B:%s%d%s) | Cur B:%s%d", c_gray, c_cyan, rage_debug.pred_status, c_gray, c_cyan, rage_debug.pred_body_dmg, c_gray, c_white, rage_debug.cur_body_dmg))
        renderer_text(x + 8, y + 46, 255, 255, 255, 255, "d", 0, string_format("%sState: %s%s", c_gray, c_white, rage_debug.threat_state))

    elseif style == "Terminal Bracket" then
        state.panel_w, state.panel_h = 265, 52
        local lines = {
            string_format("%s[ %s%s %s] %s%s", c_gray, c_stat, rage_debug.short_status, c_gray, c_white, rage_debug.blocker_text),
            string_format("%s[ %sAIM %s] hc: %s%d%% %s(%s) | dmg: %s%d %s(%s)", c_gray, c_acc, c_gray, hc_col, rage_debug.active_hc, c_gray, rage_debug.hc_reason, dmg_col, rage_debug.active_dmg, c_gray, rage_debug.dmg_reason),
            string_format("%s[ %sPRD %s] %s%s %s| cur_b:%s%d %spred_b:%s%d", c_gray, c_acc, c_gray, c_cyan, rage_debug.pred_status, c_gray, c_white, rage_debug.cur_body_dmg, c_gray, c_cyan, rage_debug.pred_body_dmg),
            string_format("%s[ %sRES %s] %s%s %s| baim:%s%s", c_gray, c_acc, c_gray, c_green, rage_debug.threat_state, c_gray, baim_col, rage_debug.baim_mode)
        }
        for i = 1, #lines do renderer_text(x, y + (i - 1) * 13, 255, 255, 255, 255, "d", 0, lines[i]) end

    elseif style == "Cyber HUD Bars" then
        state.panel_w, state.panel_h = 165, 65
        local best_dmg = math_max(rage_debug.cur_head_dmg, rage_debug.cur_body_dmg, rage_debug.pred_body_dmg)
        local req_dmg = math_max(1, math_min(rage_debug.active_dmg, rage_debug.threat_hp > 0 and rage_debug.threat_hp or 100))
        local dmg_frac = math_min(1, best_dmg / req_dmg)
        local hc_frac  = math_min(1, rage_debug.active_hc * 0.01)

        renderer_text(x, y, 255, 255, 255, 255, "bd", 0, c_acc .. "SEGFAULT HUD " .. c_gray .. "// " .. c_stat .. rage_debug.short_status)
        renderer_text(x, y + 16, 200, 200, 210, 255, "-d", 0, string_format("DMG: %d/%d | %s", best_dmg, req_dmg, rage_debug.pred_status))
        renderer_rectangle(x, y + 26, 155, 5, 15, 15, 20, 190)
        renderer_gradient(x + 1, y + 27, math_floor(153 * dmg_frac), 3, bc[1], bc[2], bc[3], 255, 135, 255, 140, 255, true)

        renderer_text(x, y + 35, 200, 200, 210, 255, "-d", 0, string_format("HC: %d%% | %s", rage_debug.active_hc, rage_debug.threat_state))
        renderer_rectangle(x, y + 45, 155, 5, 15, 15, 20, 190)
        renderer_gradient(x + 1, y + 46, math_floor(153 * hc_frac), 3, ar, ag, ab, 255, 115, 220, 255, 255, true)

    elseif style == "Crosshair Sub-Text" then
        local cx = sizeX * 0.5
        local cy = sizeY * 0.5 + 95
        local line1 = string_format("%s[%s] %sHC:%s%d%% %sDMG:%s%d", c_stat, rage_debug.short_status, c_gray, hc_col, rage_debug.active_hc, c_gray, dmg_col, rage_debug.active_dmg)
        local line2 = string_format("%sPRED:%s%s %sBAIM:%s%s %s[%s]", c_gray, c_cyan, rage_debug.pred_status, c_gray, baim_col, string_upper(rage_debug.baim_mode), c_green, rage_debug.threat_state)
        local w1 = renderer.measure_text("-cd", line1)
        local w2 = renderer.measure_text("-cd", line2)
        renderer_text(cx + ((w1 + 2) * 0.5) * scopedFraction, cy, 255, 255, 255, 255, "-cd", 0, line1)
        renderer_text(cx + ((w2 + 2) * 0.5) * scopedFraction, cy + 10, 255, 255, 255, 255, "-cd", 0, line2)

    elseif style == "Top Status Ribbon" then
        local ribbon_str = string_format(
            "%sSEGFAULT %s| %s%s %s| TGT: %s%s (%s) %s| HC: %s%d%% %s| DMG: %s%d %s| PRED: %s%s",
            c_acc, c_gray, c_stat, rage_debug.short_status,
            c_gray, c_white, rage_debug.threat_name, rage_debug.threat_state,
            c_gray, hc_col, rage_debug.active_hc,
            c_gray, dmg_col, rage_debug.active_dmg,
            c_gray, c_cyan, rage_debug.pred_status
        )
        local plain_str = string_format(
            "SEGFAULT | %s | TGT: %s (%s) | HC: %d%% | DMG: %d | PRED: %s",
            rage_debug.short_status, rage_debug.threat_name, rage_debug.threat_state, rage_debug.active_hc,
            rage_debug.active_dmg, rage_debug.pred_status
        )
        local tw = renderer.measure_text("", plain_str)
        state.panel_w, state.panel_h = tw + 16, 20
        renderer_rectangle(x, y, tw + 16, 20, 12, 12, 16, 205)
        renderer_gradient(x, y + 18, tw + 16, 2, ar, ag, ab, 255, bc[1], bc[2], bc[3], 255, true)
        renderer_text(x + 8, y + 3, 255, 255, 255, 255, "", 0, ribbon_str)
    end
end

-- =========================================================================
-- БЕЗБАГОВЫЙ RGBA РЕНДЕР (Reflux Engine Anti-Aliasing)
-- =========================================================================
local clamp01 = function(x) return math_min(math_max(x, 0), 1) end
local texture_cache = {}

-- Генератор сырых пикселей
local function create_bitmap(w, h, pixel_fn)
    local px = {}
    for y = 0, h - 1 do
        for x = 0, w - 1 do
            local c, a = pixel_fn(x + 0.5, y + 0.5)
            px[#px + 1] = string.char(c[1], c[2], c[3], math_floor(a * 255 + 0.5))
        end
    end
    return renderer.load_rgba(table.concat(px), w, h)
end

-- Функция математического сглаживания круга
local function get_disk_fn(cx, cy, r, color)
    return function(x, y)
        local a = clamp01(r - math_sqrt((x - cx) ^ 2 + (y - cy) ^ 2) + 0.5)
        return color, a
    end
end

-- Кэширование сгенерированных текстур для углов, чтобы не убивать FPS
local function get_corner_textures(r)
    local key = 'corners_' .. r
    if not texture_cache[key] then
        local list = {}
        local centers = { { r, r }, { 0, r }, { r, 0 }, { 0, 0 } }
        for i, q in ipairs(centers) do
            list[i] = create_bitmap(r, r, get_disk_fn(q[1], q[2], r, {255, 255, 255}))
        end
        texture_cache[key] = list
    end
    return texture_cache[key]
end

-- Отрисовка прямоугольника с идеальными (запеченными) скруглениями
local function draw_smooth_rect(x, y, w, h, r, color, a)
    if a < 1 or w < 1 or h < 1 then return end
    r = math_min(math_floor(r), math_floor(math_min(w, h) / 2))
    
    if r > 0 then
        local tex = get_corner_textures(r)
        renderer.texture(tex[1], x, y, r, r, color[1], color[2], color[3], a, 'f')
        renderer.texture(tex[2], x + w - r, y, r, r, color[1], color[2], color[3], a, 'f')
        renderer.texture(tex[3], x, y + h - r, r, r, color[1], color[2], color[3], a, 'f')
        renderer.texture(tex[4], x + w - r, y + h - r, r, r, color[1], color[2], color[3], a, 'f')
    end

    renderer.rectangle(x + r, y, w - 2 * r, h, color[1], color[2], color[3], a)
    if h > 2 * r then
        renderer.rectangle(x, y + r, r, h - 2 * r, color[1], color[2], color[3], a)
        renderer.rectangle(x + w - r, y + r, r, h - 2 * r, color[1], color[2], color[3], a)
    end
end

local function draw_reflux_panel(x, y, w, h, bg_a, out_a)
    local bg_r, bg_g, bg_b = 15, 15, 19
    local out_r, out_g, out_b = 58, 58, 64
    local radius = 6
    
    if out_a > 0 then
        draw_smooth_rect(x - 1, y - 1, w + 2, h + 2, radius, {out_r, out_g, out_b}, out_a)
    end
    if bg_a > 0 then
        draw_smooth_rect(x, y, w, h, radius - 1, {bg_r, bg_g, bg_b}, bg_a)
    end
end

-- =========================================================================
-- CLEAN TELEMETRY WATERMARK
-- =========================================================================
local function draw_modern_anime_watermark(sizeX, sizeY)
    if not ui_get(menu_refs.vis_watermark_enable) then return end
    
    local ft = globals.absoluteframetime()
    if ft > 0 then
        state.fps_accum = lerp(state.fps_accum, 1 / ft, 0.1)
        state.last_fps = math_floor(state.fps_accum)
    end
    
    local ping = math_floor((client.latency() or 0) * 1000)
    local var = string_format("%.2f", globals.absoluteframetime() * 100)
    local tickrate = math_floor(1 / globals.tickinterval())
    local username = "SEGFAULT"
    local profile_name = "user"
    
    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local text_brand = username
    local brand_w = renderer.measure_text("b", text_brand)
    local sep_w = renderer.measure_text("", "  ·  ")
    
    local pad_left = 12
    local pad_right = 14
    
    local parts = {
        { profile_name, {255, 255, 255} },
        { "  ·  ", {152, 148, 176} },
        { tostring(state.last_fps), {255, 255, 255} },
        { " fps", {152, 148, 176} },
        { "  ·  ", {152, 148, 176} },
        { var, {255, 255, 255} },
        { " var", {152, 148, 176} },
        { "  ·  ", {152, 148, 176} },
        { tostring(ping), {255, 255, 255} },
        { " ms", {152, 148, 176} },
        { "  ·  ", {152, 148, 176} },
        { "online", {255, 255, 255} },
        { "  ·  ", {152, 148, 176} },
        { tostring(tickrate), {255, 255, 255} },
        { " tick", {152, 148, 176} },
    }
    
    local metrics_w = 0
    for i = 1, #parts do
        metrics_w = metrics_w + renderer.measure_text("", parts[i][1])
    end
    
    local total_w = pad_left + brand_w + sep_w + metrics_w + pad_right
    local total_h = 26
    
    local wx = sizeX - total_w - 20
    local wy = 14
    
    -- Вызываем идеальный рендер панели через текстуры
    draw_reflux_panel(wx, wy, total_w, total_h, 215, 200)

    local text_x = wx + pad_left
    local text_y = wy + math_floor(total_h / 2) - 6
    
    renderer_text(text_x, text_y, ar, ag, ab, 255, "b", 0, text_brand)
    text_x = text_x + brand_w
    
    renderer_text(text_x, text_y, 152, 148, 176, 255, "", 0, "  ·  ")
    text_x = text_x + sep_w
    
    local cx = text_x
    for i = 1, #parts do
        local p = parts[i]
        local str, col = p[1], p[2]
        renderer_text(cx, text_y, col[1], col[2], col[3], 255, "", 0, str)
        cx = cx + renderer.measure_text("", str)
    end
end

-- =========================================================================
-- CLEAN KEYBINDS PANEL (TELEMETRY STYLE)
-- =========================================================================
local function draw_keybinds_panel(sizeX, sizeY)
    if not ui_get(menu_refs.vis_keybinds_enable) then return end
    
    local active_binds = {}
    
    local isCharged = antiaim_funcs.get_double_tap()
    if refs.dt and ui_get(refs.dt[1]) and (refs.dt[2] == nil or ui_get(refs.dt[2])) then
        table.insert(active_binds, {name = "Double tap", mode = isCharged and "ready" or "recharging"})
    end
    if refs.os and ui_get(refs.os[1]) and (refs.os[2] == nil or ui_get(refs.os[2])) then
        table.insert(active_binds, {name = "Hide shots", mode = "toggled"})
    end
    if refs.sp and ui_get(refs.sp[1]) then
        table.insert(active_binds, {name = "Safe point", mode = "forced"})
    end
    if refs.ba and ui_get(refs.ba[1]) then
        table.insert(active_binds, {name = "Body aim", mode = "forced"})
    elseif state.auto_baim_active then
        table.insert(active_binds, {name = "Auto body aim", mode = "active"})
    end
    if refs.fs and ui_get(refs.fs[1]) and (refs.fs[2] == nil or ui_get(refs.fs[2])) then
        table.insert(active_binds, {name = "Freestanding", mode = "toggled"})
    end
    if refs.quick_peek and ui_get(refs.quick_peek[1]) and ui_get(refs.quick_peek[2]) then
        table.insert(active_binds, {name = "Quick peek", mode = "active"})
    end
    if ui_get(menu_refs.hc_enable) and ui_get(menu_refs.hc_hotkey) then
        table.insert(active_binds, {name = "Hitchance override", mode = "held"})
    end

    if #active_binds == 0 and not ui.is_menu_open() then return end

    local pad_left = 12
    local pad_right = 14
    local brand_str = "SEGFAULT"
    local sep_str = "  ·  "
    local title_str = "keybinds"
    
    local brand_w = renderer.measure_text("b", brand_str)
    local sep_w = renderer.measure_text("", sep_str)
    local title_w = renderer.measure_text("", title_str)
    
    local max_w = brand_w + sep_w + title_w
    for i, bind in ipairs(active_binds) do
        local bw = renderer.measure_text("", bind.name) + renderer.measure_text("", bind.mode) + 30
        if bw > max_w then max_w = bw end
    end
    
    local total_w = math_max(160, pad_left + max_w + pad_right)
    local item_h = 16
    local header_h = 26
    local total_h = header_h + (#active_binds * item_h) + (#active_binds > 0 and 6 or 0)
    
    local x = ui_get(menu_refs.vis_keybinds_x)
    local y = ui_get(menu_refs.vis_keybinds_y)
    local mx, my = ui.mouse_position()
    local left_down = client.key_state(0x01)
    
    if ui.is_menu_open() then
        local hovered = (mx >= x and mx <= x + total_w and my >= y and my <= y + total_h)
        if left_down then
            if not state.kb_is_dragging and hovered then
                state.kb_is_dragging = true
                state.kb_drag_offset_x = mx - x
                state.kb_drag_offset_y = my - y
            end
            if state.kb_is_dragging then
                x = math_max(0, math_min(sizeX - total_w, mx - state.kb_drag_offset_x))
                y = math_max(0, math_min(sizeY - total_h, my - state.kb_drag_offset_y))
                ui_set(menu_refs.vis_keybinds_x, x)
                ui_set(menu_refs.vis_keybinds_y, y)
            end
        else
            state.kb_is_dragging = false
        end
    else
        state.kb_is_dragging = false
    end

    -- Вызываем идеальный рендер панели через текстуры
    draw_reflux_panel(x, y, total_w, total_h, 215, 200)
    
    local ar, ag, ab = ui_get(menu_refs.vis_ci_color)
    local text_x = x + pad_left
    local text_y = y + math_floor(header_h / 2) - 6
    
    renderer_text(text_x, text_y, ar, ag, ab, 255, "b", 0, brand_str)
    text_x = text_x + brand_w
    renderer_text(text_x, text_y, 152, 148, 176, 255, "", 0, sep_str)
    text_x = text_x + sep_w
    renderer_text(text_x, text_y, 255, 255, 255, 255, "", 0, title_str)
    
    if #active_binds > 0 then
        renderer_rectangle(x + pad_left, y + header_h - 1, total_w - pad_left - pad_right, 1, 152, 148, 176, 40)
    end
    
    local cur_y = y + header_h + 3
    for i, bind in ipairs(active_binds) do
        renderer_text(x + pad_left, cur_y, 220, 220, 230, 255, "", 0, bind.name)
        local mw = renderer.measure_text("", bind.mode)
        renderer_text(x + total_w - pad_right - mw, cur_y, 152, 148, 176, 255, "", 0, bind.mode)
        cur_y = cur_y + item_h
    end
end

local function animate_text(time, str, r, g, b, a)
    local t_out, t_out_iter = {}, 1
    local r_add, g_add, b_add, a_add = (255 - r), (255 - g), (255 - b), (165 - a)
    for i = 1, #str do
        local iter = (i - 1) / (#str - 1) + time
        local cos_val = math_abs(math_cos(iter))
        t_out[t_out_iter] = "\a" .. string_format('%.2x%.2x%.2x%.2x', r + r_add * cos_val, g + g_add * cos_val, b + b_add * cos_val, a + a_add * cos_val)
        t_out[t_out_iter + 1] = string.sub(str, i, i)
        t_out_iter = t_out_iter + 2
    end
    return t_out
end

client.set_event_callback("paint_ui", function()
    if not ui_get(menu_refs.master_switch) or not entity_get_local_player() then return end

    local sizeX, sizeY = client.screen_size()
    draw_custom_weapon_grid(sizeX, sizeY)

    if ui_get(menu_refs.vis_tp_enable) then
        set_cvar_cached("c_maxpitch", ui_get(menu_refs.vis_tp_pitch))
        set_cvar_cached("c_maxyaw", ui_get(menu_refs.vis_tp_yaw))
        set_cvar_cached("c_minyaw", ui_get(menu_refs.vis_tp_yaw))
        set_cvar_cached("cl_pitchup", ui_get(menu_refs.vis_tp_pitch_up))
        set_cvar_cached("cl_pitchdown", ui_get(menu_refs.vis_tp_pitch_down))
        set_cvar_cached("cam_idealpitch", ui_get(menu_refs.vis_tp_pitch_down))

        local target_distance = ui_get(menu_refs.vis_tp_dist)
        local zoom_speed = ui_get(menu_refs.vis_tp_zoom)

        if zoom_speed == 0 then
            state.current_distance = target_distance
        else
            local delta = (target_distance - state.current_distance) / zoom_speed
            if (delta > 0 and state.current_distance < target_distance) or (delta < 0 and state.current_distance > target_distance) then
                state.current_distance = state.current_distance + delta
            end
        end

        local dist_int = math_floor(state.current_distance)
        set_cvar_cached("c_mindistance", dist_int)
        set_cvar_cached("c_maxdistance", dist_int)
    else
        set_cvar_cached("c_maxpitch", 0)
        set_cvar_cached("c_maxyaw", 0)
        set_cvar_cached("c_minyaw", 0)
        set_cvar_cached("cl_pitchup", 90)
        set_cvar_cached("cl_pitchdown", 90)
        set_cvar_cached("c_mindistance", 100)
        set_cvar_cached("c_maxdistance", 100)
    end
end)

client.set_event_callback("paint", function()
    if not ui_get(menu_refs.master_switch) then return end

    local sizeX, sizeY = client.screen_size()
    local local_player = entity_get_local_player()
    local is_me_alive = local_player ~= nil and entity_is_alive(local_player)

    if is_me_alive then
        local weapon = entity.get_player_weapon(local_player)
        local scopeLevel = weapon and (entity_get_prop(weapon, 'm_zoomLevel') or 0) or 0
        local scoped = entity_get_prop(local_player, 'm_bIsScoped') == 1
        local act = scopeLevel > 0 and scoped
        local time = globals.frametime() * 30
        if act then
            state.scopedFraction = state.scopedFraction < 1 and (state.scopedFraction + time) or 1
        else
            state.scopedFraction = state.scopedFraction > 0 and (state.scopedFraction - time) or 0
        end
    end

    draw_modern_anime_watermark(sizeX, sizeY)
    draw_keybinds_panel(sizeX, sizeY)
    draw_rage_debug_panel(sizeX, sizeY, state.scopedFraction)
    draw_dt_telemetry_bar(sizeX, sizeY)

    if ui_get(menu_refs.debug_panel_enable) then
        local current_threat = client.current_threat()
        draw_threat_prediction_debug(local_player, current_threat)
    end

    if ui_get(menu_refs.hpbar_enable) and refs.esp_hpbar ~= nil then
        ui_set(refs.esp_hpbar[1], false)
    end

    if ui_get(menu_refs.vis_ar_enable) then
        local mode = ui_get(menu_refs.vis_ar_mode)
        local ratio = 0
        if mode == "4:3" then ratio = 4.0 / 3.0
        elseif mode == "16:10" then ratio = 16.0 / 10.0
        elseif mode == "5:4" then ratio = 5.0 / 4.0
        elseif mode == "Custom" then ratio = ui_get(menu_refs.vis_ar_custom) * 0.01 end

        if ratio > 0 then set_cvar_cached("r_aspectratio", string_format("%.2f", ratio))
        else set_cvar_cached("r_aspectratio", "0") end
    end

    if ui_get(menu_refs.hpbar_enable) and local_player ~= nil then
        local r, g, b = ui_get(menu_refs.hpbar_color1)
        local r2, g2, b2 = ui_get(menu_refs.hpbar_color2)
        local r3, g3, b3 = ui_get(menu_refs.hpbar_color3)
        local use_grad = ui_get(menu_refs.hpbar_gradient)

        local force_teammates = refs.esp_teammates ~= nil and ui_get(refs.esp_teammates[1]) or false
        if not is_me_alive then
            local m_iObserverMode = entity_get_prop(local_player, "m_iObserverMode")
            if m_iObserverMode == 4 or m_iObserverMode == 5 then
                local spectated_ent = entity_get_prop(local_player, "m_hObserverTarget")
                if spectated_ent ~= nil and entity.is_enemy(spectated_ent) then force_teammates = true end
            end
        end

        local enemy_players = entity_get_players(not force_teammates)
        for i = 1, #enemy_players do
            local e = enemy_players[i]
            if is_me_alive or not force_teammates or (force_teammates and not is_me_alive and not entity.is_enemy(e)) then
                local x1, y1, _, y2 = entity.get_bounding_box(e)
                if x1 ~= nil and y1 ~= nil and not entity_is_dormant(e) then
                    local hp = entity_get_prop(e, "m_iHealth")
                    if hp ~= nil then
                        local height = y2 - y1 + 2
                        y1 = y1 - 1
                        local leftside = x1 - 5
                        local percentage = hp * 0.01
                        local name = entity.get_player_name(e)

                        renderer_rectangle(leftside - 1, y1, 4, height, 20, 20, 20, 150)
                        local new_r, new_g, new_b = lerp(r2, r, percentage), lerp(g2, g, percentage), lerp(b2, b, percentage)
                        local bar_top = math_ceil(y2 - (height * percentage)) + 2
                        local bar_h = math_floor(height * percentage) - 2

                        if use_grad then
                            renderer_gradient(leftside, bar_top, 2, bar_h, new_r, new_g, new_b, 255, r2, g2, b2, 255, false)
                        else
                            renderer_rectangle(leftside, bar_top, 2, bar_h, new_r, new_g, new_b, 255)
                        end
                        if hp < 100 then
                            renderer_text(leftside - 2, y2 - (height * percentage) + 2, 255, 255, 255, 255, "-cd", 0, hp)
                        end
                        state.hp_players[name] = { ent = e, health = hp, health_percentage = percentage, active = false, alpha = 255 }
                    end
                end
            end
        end

        if is_me_alive then
            for k, v in pairs(state.hp_players) do
                if not v.active and entity_is_alive(v.ent) then
                    local x1, y1, _, y2 = entity.get_bounding_box(v.ent)
                    if x1 ~= nil and y1 ~= nil then
                        local height = y2 - y1 + 2
                        y1 = y1 - 1
                        local leftside = x1 - 5
                        local percentage = v.health_percentage
                        local hp = v.health
                        renderer_rectangle(leftside - 1, y1, 4, height, 20, 20, 20, 150 * (v.alpha / 255))
                        v.alpha = v.alpha - 0.25
                        local new_r, new_g, new_b = lerp(r2, r, percentage), lerp(g2, g, percentage), lerp(b2, b, percentage)
                        local bar_top = math_ceil(y2 - (height * percentage)) + 2
                        local bar_h = math_floor(height * percentage) - 2
                        if use_grad then
                            renderer_gradient(leftside, bar_top, 2, bar_h, new_r, new_g, new_b, v.alpha, r2, g2, b2, v.alpha, false)
                        else
                            renderer_rectangle(leftside, bar_top, 2, bar_h, new_r, new_g, new_b, v.alpha)
                        end
                        if hp < 100 then
                            renderer_text(leftside - 2, y2 - (height * percentage) + 2, 255, 255, 255, v.alpha, "-cd", 0, hp)
                        end
                    end
                end
                if v.alpha < 0 then state.hp_players[k] = nil end
            end
        end
    end

    if ui_get(menu_refs.jc_enable) then
        if ui_get(menu_refs.jc_indicator) then
            if state.jc_currently_resolving then renderer_indicator(144, 255, 144, 255, "JC: " .. state.jc_active_mode_str)
            else renderer_indicator(150, 220, 255, 255, "JC: IDLE") end
        end
        if ui_get(menu_refs.jc_showtarget) and state.jc_active_target_name ~= nil then
            renderer_indicator(255, 255, 255, 255, string_format("Target: %s [%d°]", state.jc_active_target_name, state.jc_active_target_desync))
        end
    end

    if ui_get(menu_refs.hm_enable) then
        if globals.curtime() > state.hitmarker_time then
            state.hitmarker_alpha = math_max(0, state.hitmarker_alpha - globals.frametime() * 800)
        end
        if state.hitmarker_alpha > 0 then
            local r, g, b = ui_get(menu_refs.hm_color)
            local size = ui_get(menu_refs.hm_size)
            local gap = ui_get(menu_refs.hm_gap)
            local cx, cy = sizeX * 0.5, sizeY * 0.5
            local a = state.hitmarker_alpha
            renderer.line(cx - size - gap, cy - size - gap, cx - gap, cy - gap, r, g, b, a)
            renderer.line(cx + size + gap, cy - size - gap, cx + gap, cy - gap, r, g, b, a)
            renderer.line(cx - size - gap, cy + size + gap, cx - gap, cy + gap, r, g, b, a)
            renderer.line(cx + size + gap, cy + size + gap, cx + gap, cy + gap, r, g, b, a)
        end
    end

    if ui_get(menu_refs.vis_logs_enable) then
        local offsetY = 0
        local curtime = globals.curtime()
        local ft = globals.frametime()
        for i = #state.log_notifications, 1, -1 do
            local notif = state.log_notifications[i]
            if notif.time + 3.5 - curtime <= 0 and notif.fraction <= 0 then
                table.remove(state.log_notifications, i)
            end
        end
        for i = 1, #state.log_notifications do
            local notif = state.log_notifications[i]
            if notif.time + 3.5 - curtime > 0 then
                notif.fraction = math_min(notif.fraction + ft / 0.4, 1)
            else
                notif.fraction = math_max(notif.fraction - ft / 0.4, 0)
            end
            local r, g, b, a = unpack(notif.color)
            local _, strh = renderer.measure_text("c", notif.string)
            offsetY = offsetY + strh + 8
            renderer_text(sizeX * 0.5 + 1, sizeY - 220 + offsetY + 1, 0, 0, 0, a * notif.fraction * 0.7, "c", 0, notif.string)
            renderer_text(sizeX * 0.5, sizeY - 220 + offsetY, r, g, b, a * notif.fraction, "c", 0, notif.string)
        end
    end

    if not ui_get(menu_refs.vis_ci_enable) or not is_me_alive then return end

    local main_r, main_g, main_b = ui_get(menu_refs.vis_ci_color)
    local flags = (ui_get(menu_refs.vis_ci_font) == "minimal") and "c-d-" or "cd"
    local onground = bit.band(entity_get_prop(local_player, "m_fFlags") or 0, 1) ~= 0

    local current_state = "STAND"
    if not onground then current_state = "AIR"
    elseif rage_debug.my_speed >= 5 then current_state = "MOVE" end

    local globalMoveY, indCount, yDefault = 9, 0, 22
    local indY = renderer.measure_text(flags, "DT") - 2
    local cx, cy = sizeX * 0.5, sizeY * 0.5
    local sf = state.scopedFraction

    local isCharged = antiaim_funcs.get_double_tap()
    local isDt = refs.dt ~= nil and ui_get(refs.dt[1]) and (refs.dt[2] == nil or ui_get(refs.dt[2]))
    local isOs = refs.os ~= nil and ui_get(refs.os[1]) and (refs.os[2] == nil or ui_get(refs.os[2]))
    local isFs = refs.fs ~= nil and ui_get(refs.fs[1]) and (refs.fs[2] == nil or ui_get(refs.fs[2]))
    local isSp = (refs.sp ~= nil and ui_get(refs.sp[1]))
    local isBa = (refs.ba ~= nil and ui_get(refs.ba[1])) or state.auto_baim_active
    local isJc = ui_get(menu_refs.jc_enable) and ui_get(menu_refs.jc_indicator)
    local isHc = ui_get(menu_refs.hc_enable) and ui_get(menu_refs.hc_hotkey)
    local hc_text = ui_get(menu_refs.hc_indicator)

    local logo_text = animate_text(globals.curtime(), "SEGFAULT", main_r, main_g, main_b, 255)
    renderer_text(cx + ((renderer.measure_text(flags, "SEGFAULT") + 2) * 0.5) * sf, cy + 22, 255, 255, 255, 255, flags, nil, unpack(logo_text))
    renderer_text(cx + ((renderer.measure_text(flags, current_state) + 2) * 0.5) * sf, cy + 35, 255, 255, 255, 255, flags, 0, current_state)

    if isDt then
        local dr, dg, db = isCharged and 144 or 222, isCharged and 238 or 55, isCharged and 144 or 55
        renderer_text(cx + ((renderer.measure_text(flags, "DT") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), dr, dg, db, 255, flags, 0, "DT")
        indCount = indCount + 1
    end
    if isOs then
        renderer_text(cx + ((renderer.measure_text(flags, "HS") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), main_r, main_g, main_b, 255, flags, 0, "HS")
        indCount = indCount + 1
    end
    if isJc then
        local jr, jg, jb = state.jc_currently_resolving and 144 or 150, state.jc_currently_resolving and 255 or 220, state.jc_currently_resolving and 144 or 255
        renderer_text(cx + ((renderer.measure_text(flags, "JC") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), jr, jg, jb, 255, flags, 0, "JC")
        indCount = indCount + 1
    end
    if isHc and hc_text ~= "Off" then
        renderer_text(cx + ((renderer.measure_text(flags, hc_text) + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), 255, 255, 255, 255, flags, 0, hc_text)
        indCount = indCount + 1
    end
    if isFs then
        renderer_text(cx + ((renderer.measure_text(flags, "FS") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), 255, 255, 255, 255, flags, 0, "FS")
        indCount = indCount + 1
    end
    if isSp then
        renderer_text(cx + ((renderer.measure_text(flags, "SP") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), 255, 255, 255, 255, flags, 0, "SP")
        indCount = indCount + 1
    end
    if isBa then
        local br, bg, bb = state.auto_baim_active and 144 or 255, 255, state.auto_baim_active and 144 or 255
        renderer_text(cx + ((renderer.measure_text(flags, "BA") + 2) * 0.5) * sf, cy + yDefault + 13 + globalMoveY + (indY * indCount), br, bg, bb, 255, flags, 0, "BA")
        indCount = indCount + 1
    end
end)

client.set_event_callback("shutdown", function()
    jumpscout_fix_controller.shutdown()
    if state.hc_cache ~= nil and refs.hitchance ~= nil and refs.hitchance[1] ~= nil then ui_set(refs.hitchance[1], state.hc_cache) end
    if state.mindmg_cache ~= nil and refs.mindmg ~= nil and refs.mindmg[1] ~= nil then ui_set(refs.mindmg[1], state.mindmg_cache) end
    if state.dt_saved_sp ~= nil and refs.sp ~= nil and refs.sp[1] ~= nil then ui_set(refs.sp[1], state.dt_saved_sp) end

    set_early_stop(false)
    reset_baim_overrides()
    reset_entity_resolver()

    state.cvar_cache = {}
    client.set_cvar("c_maxpitch", 0)
    client.set_cvar("c_maxyaw", 0)
    client.set_cvar("c_minyaw", 0)
    client.set_cvar("cl_pitchup", 90)
    client.set_cvar("cl_pitchdown", 90)
    client.set_cvar("c_mindistance", 100)
    client.set_cvar("c_maxdistance", 100)
    client.set_cvar("r_aspectratio", "0")
end)

do
    local function update_viewmodel()
        if not ui_get(menu_refs.master_switch) or not ui_get(menu_refs.vis_vm_enable) then return end
        local fov = ui_get(menu_refs.vis_vm_fov)
        local x = ui_get(menu_refs.vis_vm_x) * 0.1
        local y = ui_get(menu_refs.vis_vm_y) * 0.1
        local z = ui_get(menu_refs.vis_vm_z) * 0.1
        client.exec(string_format("viewmodel_fov %d; viewmodel_offset_x %.1f; viewmodel_offset_y %.1f; viewmodel_offset_z %.1f", fov, x, y, z))
    end

    ui.set_callback(menu_refs.vis_vm_fov, update_viewmodel)
    ui.set_callback(menu_refs.vis_vm_x, update_viewmodel)
    ui.set_callback(menu_refs.vis_vm_y, update_viewmodel)
    ui.set_callback(menu_refs.vis_vm_z, update_viewmodel)
    ui.set_callback(menu_refs.vis_vm_enable, update_viewmodel)
end

-- =========================================================================
-- OPTIMIZED DYNAMIC INTERFACE VISIBILITY & GROUPING LOGIC
-- =========================================================================
handle_logic = function()
    local m = menu_refs
    if m.master_switch == nil then return end
    local is_active = ui_get(m.master_switch)
    local current_tab = m.tab_selector ~= nil and ui_get(m.tab_selector) or nil

    if is_active and not state.was_active then print_logo() end
    state.was_active = is_active

    if m.tab_selector ~= nil then ui_set_visible(m.tab_selector, is_active) end

    for tab_name, elements in pairs(tab_elements) do
        local should_show = is_active and (current_tab == tab_name)
        for i = 1, #elements do
            if elements[i] ~= nil then ui_set_visible(elements[i], should_show) end
        end
    end

    local rage_active = is_active and (current_tab == "⚔ Rage")
    if m.mindmg_boost_enable ~= nil then ui_set_visible(m.mindmg_boost_enable, rage_active) end
    if m.mindmg_hp_threshold ~= nil then ui_set_visible(m.mindmg_hp_threshold, rage_active and ui_get(m.mindmg_boost_enable)) end

    local aimtools_active = is_active and (current_tab == "🎯 Aim Tools")
    
    -- Группа 1: Резольвер
    if m.jc_enable ~= nil then ui_set_visible(m.jc_enable, aimtools_active) end
    local jc_enabled = aimtools_active and m.jc_enable ~= nil and ui_get(m.jc_enable)
    if m.jc_showtarget ~= nil then ui_set_visible(m.jc_showtarget, jc_enabled) end
    if m.jc_indicator ~= nil then ui_set_visible(m.jc_indicator, jc_enabled) end

    if m.js_fix_enable ~= nil then ui_set_visible(m.js_fix_enable, aimtools_active) end
    if m.js_fix_dist ~= nil then ui_set_visible(m.js_fix_dist, aimtools_active and ui_get(m.js_fix_enable)) end

    -- Группа 2: Предикшн и Force Shot
    if m.unsafe_recharge ~= nil then ui_set_visible(m.unsafe_recharge, aimtools_active) end
    if m.early_stop_def ~= nil then ui_set_visible(m.early_stop_def, aimtools_active) end
    if m.auto_baim_peek ~= nil then ui_set_visible(m.auto_baim_peek, aimtools_active) end

    local rp_on = aimtools_active and (m.real_pred_enable ~= nil and ui_get(m.real_pred_enable) == true)
    local rp_adaptive = rp_on and (m.real_pred_adaptive ~= nil and ui_get(m.real_pred_adaptive) == true)
    if m.real_pred_enable ~= nil then ui_set_visible(m.real_pred_enable, aimtools_active) end
    if m.real_pred_adaptive ~= nil then ui_set_visible(m.real_pred_adaptive, rp_on) end
    if m.real_pred_mode ~= nil then ui_set_visible(m.real_pred_mode, rp_on) end
    if m.real_pred_ticks ~= nil then ui_set_visible(m.real_pred_ticks, rp_on) end

    local fs_peek_on = aimtools_active and (m.force_shot_peek ~= nil and ui_get(m.force_shot_peek) == true)
    if m.force_shot_peek ~= nil then ui_set_visible(m.force_shot_peek, aimtools_active) end
    if m.force_shot_key ~= nil then ui_set_visible(m.force_shot_key, fs_peek_on) end
    if m.force_shot_hc_red ~= nil then ui_set_visible(m.force_shot_hc_red, fs_peek_on) end
    if m.force_shot_stop ~= nil then ui_set_visible(m.force_shot_stop, fs_peek_on) end

    -- Группа 3: Автостоп
    local on_land_on = aimtools_active and (m.on_land_enable ~= nil and ui_get(m.on_land_enable) == true)
    if m.on_land_enable ~= nil then ui_set_visible(m.on_land_enable, aimtools_active) end
    if m.on_land_mode ~= nil then ui_set_visible(m.on_land_mode, on_land_on) end
    if m.on_land_weapons ~= nil then ui_set_visible(m.on_land_weapons, on_land_on) end

    local in_air_on = aimtools_active and (m.in_air_stop ~= nil and ui_get(m.in_air_stop) == true)
    if m.in_air_stop ~= nil then ui_set_visible(m.in_air_stop, aimtools_active) end
    if m.in_air_dist ~= nil then ui_set_visible(m.in_air_dist, in_air_on) end

    -- Группа 4: Фиксы и Хитшанс
    local dt_fix_on = aimtools_active and m.dt_fix_enable ~= nil and ui_get(m.dt_fix_enable)
    if m.dt_fix_enable ~= nil then ui_set_visible(m.dt_fix_enable, aimtools_active) end
    if m.dt_fix_weapons ~= nil then ui_set_visible(m.dt_fix_weapons, dt_fix_on) end
    if m.dt_fix_speed ~= nil then ui_set_visible(m.dt_fix_speed, dt_fix_on) end
    if m.dt_fix_hc ~= nil then ui_set_visible(m.dt_fix_hc, dt_fix_on) end

    local hc_on = aimtools_active and m.hc_enable ~= nil and ui_get(m.hc_enable)
    if m.hc_enable ~= nil then ui_set_visible(m.hc_enable, aimtools_active) end
    if m.hc_weapon ~= nil then ui_set_visible(m.hc_weapon, false) end
    if m.hc_hotkey ~= nil then ui_set_visible(m.hc_hotkey, hc_on) end
    if m.hc_indicator ~= nil then ui_set_visible(m.hc_indicator, hc_on) end

    local cur_w = m.hc_weapon ~= nil and ui_get(m.hc_weapon) or nil
    for w, items in pairs(hc_settings) do
        local show_w = hc_on and (cur_w == w)
        if items.options ~= nil then ui_set_visible(items.options, show_w) end

        local active_opts = {}
        if show_w and items.options ~= nil then
            local opts = ui_get(items.options)
            for i = 1, #opts do active_opts[opts[i]] = true end
        end

        for opt, opt_items in pairs(items) do
            if opt ~= "options" then
                local show_opt = show_w and active_opts[opt]
                if opt_items.val ~= nil then ui_set_visible(opt_items.val, show_opt) end
                if opt_items.dmg ~= nil then ui_set_visible(opt_items.dmg, show_opt and (opt == "In Air")) end
                if opt_items.dist ~= nil then ui_set_visible(opt_items.dist, show_opt) end
            end
        end
    end

    local dbg_on = aimtools_active and (m.debug_panel_enable ~= nil and ui_get(m.debug_panel_enable) == true)
    if m.debug_panel_enable ~= nil then ui_set_visible(m.debug_panel_enable, aimtools_active) end
    if m.debug_panel_style ~= nil then ui_set_visible(m.debug_panel_style, dbg_on) end
    ui_set_visible(m.debug_panel_x, false)
    ui_set_visible(m.debug_panel_y, false)

    -- Визуальные настройки (Visual Tab)
    local vis_active = is_active and (current_tab == "✦ Visual")
    local ar_enabled = vis_active and m.vis_ar_enable ~= nil and ui_get(m.vis_ar_enable)
    if m.vis_ar_mode ~= nil then ui_set_visible(m.vis_ar_mode, ar_enabled) end
    if m.vis_ar_custom ~= nil then ui_set_visible(m.vis_ar_custom, ar_enabled and (ui_get(m.vis_ar_mode) == "Custom")) end

    local tesla_enabled = vis_active and m.tesla_enable ~= nil and ui_get(m.tesla_enable)
    if m.tesla_color ~= nil then ui_set_visible(m.tesla_color, tesla_enabled) end
    if m.tesla_width ~= nil then ui_set_visible(m.tesla_width, tesla_enabled) end
    if m.tesla_radius ~= nil then ui_set_visible(m.tesla_radius, tesla_enabled) end
    if m.tesla_beams ~= nil then ui_set_visible(m.tesla_beams, tesla_enabled) end

    local hm_enabled = vis_active and m.hm_enable ~= nil and ui_get(m.hm_enable)
    if m.hm_color ~= nil then ui_set_visible(m.hm_color, hm_enabled) end
    if m.hm_size ~= nil then ui_set_visible(m.hm_size, hm_enabled) end
    if m.hm_gap ~= nil then ui_set_visible(m.hm_gap, hm_enabled) end
    if m.hm_duration ~= nil then ui_set_visible(m.hm_duration, hm_enabled) end

    local hpbar_enabled = vis_active and m.hpbar_enable ~= nil and ui_get(m.hpbar_enable)
    if m.hpbar_gradient ~= nil then ui_set_visible(m.hpbar_gradient, hpbar_enabled) end
    if m.hpbar_label1 ~= nil then ui_set_visible(m.hpbar_label1, hpbar_enabled) end
    if m.hpbar_color1 ~= nil then ui_set_visible(m.hpbar_color1, hpbar_enabled) end
    if m.hpbar_label2 ~= nil then ui_set_visible(m.hpbar_label2, hpbar_enabled) end
    if m.hpbar_color2 ~= nil then ui_set_visible(m.hpbar_color2, hpbar_enabled) end
    if m.hpbar_label3 ~= nil then ui_set_visible(m.hpbar_label3, hpbar_enabled) end
    if m.hpbar_color3 ~= nil then ui_set_visible(m.hpbar_color3, hpbar_enabled) end

    local tp_active = vis_active and m.vis_tp_enable ~= nil and ui_get(m.vis_tp_enable)
    if m.vis_tp_dist ~= nil then ui_set_visible(m.vis_tp_dist, tp_active) end
    if m.vis_tp_zoom ~= nil then ui_set_visible(m.vis_tp_zoom, tp_active) end
    if m.vis_tp_pitch ~= nil then ui_set_visible(m.vis_tp_pitch, tp_active) end
    if m.vis_tp_yaw ~= nil then ui_set_visible(m.vis_tp_yaw, tp_active) end
    if m.vis_tp_pitch_up ~= nil then ui_set_visible(m.vis_tp_pitch_up, tp_active) end
    if m.vis_tp_pitch_down ~= nil then ui_set_visible(m.vis_tp_pitch_down, tp_active) end

    local vm_active = vis_active and m.vis_vm_enable ~= nil and ui_get(m.vis_vm_enable)
    if m.vis_vm_fov ~= nil then ui_set_visible(m.vis_vm_fov, vm_active) end
    if m.vis_vm_x ~= nil then ui_set_visible(m.vis_vm_x, vm_active) end
    if m.vis_vm_y ~= nil then ui_set_visible(m.vis_vm_y, vm_active) end
    if m.vis_vm_z ~= nil then ui_set_visible(m.vis_vm_z, vm_active) end
    if m.vis_hand_knife ~= nil then ui_set_visible(m.vis_hand_knife, vm_active) end
    if m.vis_hand_weapon ~= nil then ui_set_visible(m.vis_hand_weapon, vm_active) end

    local ci_active = vis_active and m.vis_ci_enable ~= nil and ui_get(m.vis_ci_enable)
    if m.vis_ci_color ~= nil then ui_set_visible(m.vis_ci_color, ci_active) end
    if m.vis_ci_font ~= nil then ui_set_visible(m.vis_ci_font, ci_active) end
    if m.vis_watermark_enable ~= nil then ui_set_visible(m.vis_watermark_enable, vis_active) end
    if m.vis_keybinds_enable ~= nil then ui_set_visible(m.vis_keybinds_enable, vis_active) end

    if m.vis_logs_enable ~= nil then ui_set_visible(m.vis_logs_enable, vis_active) end
    if m.vis_logs_color ~= nil then ui_set_visible(m.vis_logs_color, vis_active and ui_get(m.vis_logs_enable)) end
    
    ui_set_visible(m.vis_keybinds_x, false)
    ui_set_visible(m.vis_keybinds_y, false)
end

for _, ref in pairs({
    menu_refs.master_switch, menu_refs.tab_selector, menu_refs.mindmg_boost_enable,
    menu_refs.jc_enable, menu_refs.js_fix_enable, menu_refs.jc_showtarget, menu_refs.jc_indicator,
    menu_refs.unsafe_recharge,
    menu_refs.early_stop_def, menu_refs.auto_baim_peek,
    menu_refs.real_pred_enable, menu_refs.real_pred_adaptive, menu_refs.real_pred_mode, menu_refs.real_pred_ticks,
    menu_refs.force_shot_peek, menu_refs.force_shot_key, menu_refs.force_shot_hc_red, menu_refs.force_shot_stop,
    menu_refs.on_land_enable, menu_refs.on_land_mode, menu_refs.on_land_weapons, menu_refs.in_air_stop, menu_refs.in_air_dist,
    menu_refs.debug_panel_enable, menu_refs.debug_panel_style,
    menu_refs.dt_fix_enable, menu_refs.dt_fix_weapons, menu_refs.dt_fix_speed, menu_refs.dt_fix_hc,
    menu_refs.hc_enable, menu_refs.hc_weapon,
    menu_refs.vis_ar_enable, menu_refs.vis_ar_mode, menu_refs.tesla_enable,
    menu_refs.hm_enable, menu_refs.hpbar_enable, menu_refs.vis_tp_enable,
    menu_refs.vis_vm_enable, menu_refs.vis_ci_enable, menu_refs.vis_watermark_enable, menu_refs.vis_keybinds_enable, menu_refs.vis_logs_enable,
    menu_refs.vis_telemetry_enable
}) do
    ui.set_callback(ref, handle_logic)
end

handle_logic()