#!/usr/bin/env python3
"""
Bot de Telegram: Subte Olleros <-> UADE (Archivo único autoinstalable).
Monitorea Línea D, Línea C y Línea E desde buenosaires.gob.ar / API GCBA,
filtra por tus tramos reales y permite configurar días/turnos desde Telegram.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from datetime import datetime
from enum import IntEnum
from pathlib import Path
from typing import Callable
from zoneinfo import ZoneInfo

DEFAULT_CONFIG: dict[str, object] = {
    "enabled": True,
    "timezone": "America/Argentina/Buenos_Aires",
    "origin_corner": "Av. Luis María Campos y Av. Federico Lacroze",
    "active_days": ["mar", "mie", "jue", "vie"],
    "turno": "noche",
    "alert_window": {"start": "16:30", "end": "23:30"},
    "scheduled_reports": {"enabled": True, "ida": "17:30", "vuelta": "21:45"},
    "notify_on_recovery": True,
}


# ========================================================================
# Módulo: routes.py
# ========================================================================
"""Definición de líneas, estaciones y rutas entre Olleros y UADE (Independencia)."""



# Orden real de estaciones por línea (de cabecera a cabecera)
LINE_STATIONS: dict[str, list[str]] = {
    "D": [
        "Congreso de Tucumán",
        "Juramento",
        "José Hernández",
        "Olleros",
        "Ministro Carranza",
        "Palermo",
        "Plaza Italia",
        "Scalabrini Ortiz",
        "Bulnes",
        "Agüero",
        "Pueyrredón",
        "Facultad de Medicina",
        "Callao",
        "Tribunales",
        "9 de Julio",
        "Catedral",
    ],
    "C": [
        "Retiro",
        "General San Martín",
        "Lavalle",
        "Diagonal Norte",
        "Av. de Mayo",
        "Moreno",
        "Independencia",
        "San Juan",
        "Constitución",
    ],
    "E": [
        "Retiro",
        "Catalinas",
        "Correo Central",
        "Bolívar",
        "Belgrano",
        "Independencia",
        "San José",
        "Entre Ríos",
        "Pichincha",
        "Jujuy",
        "General Urquiza",
        "Boedo",
        "Av. La Plata",
        "José María Moreno",
        "Emilio Mitre",
        "Medalla Milagrosa",
        "Varela",
        "Plaza de los Virreyes",
    ],
}

# Alias comunes que usan GCBA / Emova en partes de prensa y alertas
STATION_ALIASES: dict[str, dict[str, list[str]]] = {
    "D": {
        "Congreso de Tucumán": ["congreso de tucuman", "congreso tucuman"],
        "Juramento": ["juramento"],
        "José Hernández": ["jose hernandez", "j. hernandez"],
        "Olleros": ["olleros"],
        "Ministro Carranza": ["ministro carranza", "carranza"],
        "Palermo": ["palermo"],
        "Plaza Italia": ["plaza italia"],
        "Scalabrini Ortiz": ["scalabrini ortiz", "r. scalabrini ortiz"],
        "Bulnes": ["bulnes"],
        "Agüero": ["aguero"],
        "Pueyrredón": ["pueyrredon"],
        "Facultad de Medicina": ["facultad de medicina", "fac. de medicina"],
        "Callao": ["callao"],
        "Tribunales": ["tribunales"],
        "9 de Julio": ["9 de julio", "nueve de julio"],
        "Catedral": ["catedral"],
    },
    "C": {
        "Retiro": ["retiro"],
        "General San Martín": ["general san martin", "gral. san martin", "san martin"],
        "Lavalle": ["lavalle"],
        "Diagonal Norte": ["diagonal norte", "diag. norte"],
        "Av. de Mayo": ["av. de mayo", "avenida de mayo", "av de mayo"],
        "Moreno": ["moreno"],
        "Independencia": ["independencia"],
        "San Juan": ["san juan"],
        "Constitución": ["constitucion"],
    },
    "E": {
        "Retiro": ["retiro"],
        "Catalinas": ["catalinas"],
        "Correo Central": ["correo central"],
        "Bolívar": ["bolivar"],
        "Belgrano": ["belgrano"],
        "Independencia": ["independencia"],
        "San José": ["san jose"],
        "Entre Ríos": ["entre rios", "entre rios - rodolfo walsh"],
        "Pichincha": ["pichincha"],
        "Jujuy": ["jujuy"],
        "General Urquiza": ["general urquiza", "gral. urquiza", "urquiza"],
        "Boedo": ["boedo"],
        "Av. La Plata": ["av. la plata", "avenida la plata", "av la plata"],
        "José María Moreno": ["jose maria moreno", "j. m. moreno"],
        "Emilio Mitre": ["emilio mitre"],
        "Medalla Milagrosa": ["medalla milagrosa"],
        "Varela": ["varela"],
        "Plaza de los Virreyes": ["plaza de los virreyes", "virreyes"],
    },
}


@dataclass(frozen=True)
class LegSpec:
    """Tramo de una línea usado en el viaje."""

    line: str
    origin: str
    destination: str

    @property
    def critical_stations(self) -> set[str]:
        """Estaciones donde subís, combinás o bajás (si cierran, bloquean el tramo)."""
        return {self.origin, self.destination}

    @property
    def segment_stations(self) -> list[str]:
        """Todas las estaciones por las que pasa el tren en este tramo (inclusive)."""
        stations = LINE_STATIONS[self.line]
        idx_a = stations.index(self.origin)
        idx_b = stations.index(self.destination)
        low, high = min(idx_a, idx_b), max(idx_a, idx_b)
        return stations[low : high + 1]

    @property
    def intermediate_stations(self) -> set[str]:
        """Estaciones intermedias (si una cierra por obra, el subte pasa de largo)."""
        return set(self.segment_stations) - self.critical_stations


@dataclass(frozen=True)
class CommuteRoute:
    """Ruta completa entre Olleros y UADE (ida y vuelta)."""

    key: str
    name: str
    short_name: str
    summary_ida: str
    summary_vuelta: str
    legs: tuple[LegSpec, ...]


ROUTE_C = CommuteRoute(
    key="ruta_c",
    name="Ruta Habitual (Línea D + Línea C)",
    short_name="Línea D + C (por Diagonal Norte)",
    summary_ida="Línea D (Olleros → 9 de Julio) + combinación a Línea C (Diagonal Norte → Independencia)",
    summary_vuelta="Línea C (Independencia → Diagonal Norte) + combinación a Línea D (9 de Julio → Olleros)",
    legs=(
        LegSpec(line="D", origin="Olleros", destination="9 de Julio"),
        LegSpec(line="C", origin="Diagonal Norte", destination="Independencia"),
    ),
)

ROUTE_E = CommuteRoute(
    key="ruta_e",
    name="Ruta Alternativa (Línea D + Línea E)",
    short_name="Línea D + E (por Catedral / Bolívar)",
    summary_ida="Línea D (Olleros → Catedral) + combinación a Línea E (Bolívar → Independencia)",
    summary_vuelta="Línea E (Independencia → Bolívar) + combinación a Línea D (Catedral → Olleros)",
    legs=(
        LegSpec(line="D", origin="Olleros", destination="Catedral"),
        LegSpec(line="E", origin="Bolívar", destination="Independencia"),
    ),
)

TURNOS_PRESETS: dict[str, dict[str, object]] = {
    "manana": {
        "label": "Mañana",
        "alert_window": {"start": "06:30", "end": "13:30"},
        "scheduled_reports": {"enabled": True, "ida": "07:00", "vuelta": "11:45"},
    },
    "tarde": {
        "label": "Tarde",
        "alert_window": {"start": "12:30", "end": "19:30"},
        "scheduled_reports": {"enabled": True, "ida": "13:00", "vuelta": "17:45"},
    },
    "noche": {
        "label": "Noche",
        "alert_window": {"start": "16:30", "end": "23:30"},
        "scheduled_reports": {"enabled": True, "ida": "17:30", "vuelta": "21:45"},
    },
}

DAY_CODES = ["lun", "mar", "mie", "jue", "vie", "sab", "dom"]
DAY_NAMES = {
    "lun": "Lunes",
    "mar": "Martes",
    "mie": "Miércoles",
    "jue": "Jueves",
    "vie": "Viernes",
    "sab": "Sábado",
    "dom": "Domingo",
}


def normalize_text(text: str) -> str:
    """Convierte a minúsculas, quita tildes y normaliza espacios."""
    if not text:
        return ""
    decomposed = unicodedata.normalize("NFD", text.lower())
    without_accents = "".join(ch for ch in decomposed if unicodedata.category(ch) != "Mn")
    return " ".join(without_accents.split())


# ========================================================================
# Módulo: schedule_utils.py
# ========================================================================
"""Utilidades de horarios, días de cursada y reportes programados (hora Argentina)."""




AR_TZ = ZoneInfo("America/Argentina/Buenos_Aires")


def parse_hhmm(value: str) -> int:
    """Convierte 'HH:MM' a minutos desde las 00:00."""
    parts = value.strip().split(":")
    if len(parts) != 2:
        raise ValueError(f"Horario inválido '{value}', usá formato HH:MM (ej. 17:30)")
    hour, minute = int(parts[0]), int(parts[1])
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        raise ValueError(f"Horario fuera de rango '{value}'")
    return hour * 60 + minute


def get_day_code(dt: datetime) -> str:
    """Devuelve 'lun', 'mar', 'mie', 'jue', 'vie', 'sab' o 'dom'."""
    return DAY_CODES[dt.weekday()]


def is_within_alert_window(dt: datetime, config: dict) -> bool:
    """Indica si en la fecha/hora actual corresponde enviar alertas automáticas."""
    if not config.get("enabled", True):
        return False

    day_code = get_day_code(dt)
    active_days = [d.lower() for d in config.get("active_days", [])]
    if day_code not in active_days:
        return False

    window = config.get("alert_window") or {}
    start_min = parse_hhmm(window.get("start", "07:00"))
    end_min = parse_hhmm(window.get("end", "23:30"))
    curr_min = dt.hour * 60 + dt.minute

    if start_min <= end_min:
        return start_min <= curr_min <= end_min
    # Soporte por si la ventana cruza la medianoche (ej. 17:00 a 00:30)
    return curr_min >= start_min or curr_min <= end_min


def due_scheduled_reports(dt: datetime, config: dict, state: dict, grace_minutes: int = 45) -> list[str]:
    """
    Devuelve qué reportes fijos ('ida' / 'vuelta') corresponde enviar ahora mismo.
    Usa una ventana de tolerancia de `grace_minutes` para absorber demoras del cron
    y registra en `state['sent_reports']` para no enviar dos veces el mismo día.
    """
    if not config.get("enabled", True):
        return []

    sched = config.get("scheduled_reports") or {}
    if not sched.get("enabled", True):
        return []

    day_code = get_day_code(dt)
    if day_code not in [d.lower() for d in config.get("active_days", [])]:
        return []

    today_key = dt.strftime("%Y-%m-%d")
    already_sent = set((state.get("sent_reports") or {}).get(today_key, []))
    curr_min = dt.hour * 60 + dt.minute

    due: list[str] = []
    for slot in ("ida", "vuelta"):
        raw_time = sched.get(slot)
        if not raw_time or slot in already_sent:
            continue
        target_min = parse_hhmm(raw_time)
        if target_min <= curr_min <= target_min + grace_minutes:
            due.append(slot)

    return due


def mark_report_sent(dt: datetime, state: dict, slot: str) -> None:
    """Marca un reporte ('ida' o 'vuelta') como enviado hoy y limpia fechas viejas."""
    today_key = dt.strftime("%Y-%m-%d")
    sent_map: dict[str, list[str]] = state.setdefault("sent_reports", {})
    day_list = sent_map.setdefault(today_key, [])
    if slot not in day_list:
        day_list.append(slot)

    # Conservar solo los últimos 4 días para mantener liviano state.json
    sorted_days = sorted(sent_map.keys())
    while len(sorted_days) > 4:
        oldest = sorted_days.pop(0)
        sent_map.pop(oldest, None)


# ========================================================================
# Módulo: analyzer.py
# ========================================================================
"""Motor de análisis inteligente de estado del Subte para el viaje Olleros ↔ UADE."""





class Severity(IntEnum):
    """Nivel de impacto sobre un tramo o ruta del usuario."""

    OK = 0  # Funciona normal en el tramo del usuario
    INFO = 1  # Estación intermedia sin detención (llega igual)
    WARNING = 2  # Demoras, servicio limitado que igual cubre el tramo, o alerta general
    BLOCKED = 3  # Estación clave cerrada, tramo cortado o línea interrumpida


NORMAL_PHRASES = (
    "servicio normal",
    "normal",
    "circula con normalidad",
    "funciona con normalidad",
    "sin novedades",
    "sin alteraciones",
    "operando normalmente",
)

INTERRUPTION_KEYWORDS = (
    "interrumpid",
    "no presta servicio",
    "servicio suspendido",
    "suspendid",
    "medida de fuerza",
    "paro gremial",
    "paro de subte",
    "por paro",
    "huelga",
    "linea cerrada",
    "cerrada toda la linea",
)

LIMITED_KEYWORDS = (
    "servicio limitado",
    "recorrido limitado",
    "limitado entre",
    "circula entre",
    "circula unicamente entre",
    "solo entre",
)

CLOSURE_KEYWORDS = (
    "cerrad",
    "clausurad",
    "no se detien",
    "sin detencion",
    "no para en",
    "permanece cerrada",
    "permanecen cerradas",
)

DELAY_KEYWORDS = (
    "demora",
    "frecuencia reducida",
    "menor frecuencia",
    "inconveniente",
    "desperfecto",
    "falla tecnica",
    "problemas tecnicos",
    "manifestacion",
    "precaucion",
)


@dataclass
class LegEvaluation:
    """Resultado de evaluar un tramo puntual (ej. Línea E Bolívar ↔ Independencia)."""

    leg: LegSpec
    raw_status: str
    severity: Severity
    reasons: list[str] = field(default_factory=list)
    ignored_notes: list[str] = field(default_factory=list)
    closed_critical: list[str] = field(default_factory=list)


@dataclass
class RouteEvaluation:
    """Resultado integral para una ruta completa (Ruta C o Ruta E)."""

    route: CommuteRoute
    severity: Severity
    legs: list[LegEvaluation]
    headline: str

    @property
    def is_usable(self) -> bool:
        return self.severity < Severity.BLOCKED


@dataclass
class CommuteReport:
    """Análisis completo de las dos rutas hacia/desde UADE."""

    line_statuses: dict[str, str]
    source: str
    updated_at: str
    route_c: RouteEvaluation
    route_e: RouteEvaluation
    recommended_key: str  # "ruta_c", "ruta_e", o "alternativa_superficie"
    recommendation_text: str
    signature: str


def find_mentioned_stations(line: str, text: str) -> list[str]:
    """Detecta qué estaciones de una línea aparecen nombradas en el texto."""
    norm = normalize_text(text)
    aliases_map = STATION_ALIASES.get(line, {})
    found: list[str] = []

    # Ordenamos alias más largos primero para evitar colisiones parciales
    candidates: list[tuple[str, str]] = []
    for canonical, aliases in aliases_map.items():
        for alias in aliases:
            candidates.append((normalize_text(alias), canonical))
    candidates.sort(key=lambda item: len(item[0]), reverse=True)

    masked = norm
    for alias_norm, canonical in candidates:
        pattern = rf"(?<![a-z0-9]){re.escape(alias_norm)}(?![a-z0-9])"
        if re.search(pattern, masked):
            if canonical not in found:
                found.append(canonical)
            masked = re.sub(pattern, " ", masked)

    # Mantener orden geográfico de la línea
    station_order = LINE_STATIONS.get(line, [])
    found.sort(key=lambda st: station_order.index(st) if st in station_order else 999)
    return found


def _parse_limited_endpoints(line: str, clause: str) -> tuple[str, str] | None:
    """Si la cláusula dice 'entre X y/e Y', devuelve las dos estaciones cabecera temporales."""
    norm = normalize_text(clause)
    match = re.search(r"entre\s+(.+?)\s+(?:y|e|-|hasta)\s+(.+)", norm)
    if not match:
        stations = find_mentioned_stations(line, norm)
        if len(stations) == 2:
            return stations[0], stations[1]
        return None

    part_a, part_b = match.group(1), match.group(2)
    st_a = find_mentioned_stations(line, part_a)
    st_b = find_mentioned_stations(line, part_b)
    if st_a and st_b and st_a[0] != st_b[0]:
        return st_a[0], st_b[0]

    stations = find_mentioned_stations(line, norm)
    if len(stations) == 2:
        return stations[0], stations[1]
    return None


def _split_clauses(raw_status: str) -> list[str]:
    """Divide un parte de estado en oraciones o cláusulas independientes."""
    cleaned = re.sub(r"^(check_circle|warning|error|info)\s*", "", raw_status.strip(), flags=re.I)
    parts = re.split(r"[.;\n|]+|\s+-\s+", cleaned)
    return [p.strip() for p in parts if p and p.strip()]


def evaluate_leg(leg: LegSpec, raw_status: str) -> LegEvaluation:
    """Evalúa cómo afecta el estado de una línea a un tramo específico del usuario."""
    clean_raw = re.sub(r"^(check_circle|warning|error|info)\s*", "", (raw_status or "").strip(), flags=re.I)
    if not clean_raw:
        clean_raw = "Servicio normal"

    clauses = _split_clauses(clean_raw)
    if not clauses:
        return LegEvaluation(leg=leg, raw_status="Servicio normal", severity=Severity.OK)

    max_severity = Severity.OK
    reasons: list[str] = []
    ignored_notes: list[str] = []
    closed_critical: list[str] = []

    line_stations = LINE_STATIONS[leg.line]
    leg_low = min(line_stations.index(leg.origin), line_stations.index(leg.destination))
    leg_high = max(line_stations.index(leg.origin), line_stations.index(leg.destination))

    for clause in clauses:
        norm = normalize_text(clause)
        if not norm or any(norm == p or norm.startswith(p + " ") for p in NORMAL_PHRASES):
            continue

        matched_known_rule = False

        # 1. Interrupción total / paro
        if any(kw in norm for kw in INTERRUPTION_KEYWORDS):
            matched_known_rule = True
            max_severity = max(max_severity, Severity.BLOCKED)
            reasons.append(f"Línea {leg.line} interrumpida: «{clause}»")
            continue

        # 2. Servicio limitado entre dos cabeceras temporales
        if any(kw in norm for kw in LIMITED_KEYWORDS):
            matched_known_rule = True
            endpoints = _parse_limited_endpoints(leg.line, clause)
            if endpoints:
                st_a, st_b = endpoints
                idx_a, idx_b = line_stations.index(st_a), line_stations.index(st_b)
                active_low, active_high = min(idx_a, idx_b), max(idx_a, idx_b)
                if active_low <= leg_low and leg_high <= active_high:
                    max_severity = max(max_severity, Severity.WARNING)
                    reasons.append(
                        f"Línea {leg.line} con servicio limitado ({st_a} ↔ {st_b}): "
                        f"tu tramo {leg.origin} ↔ {leg.destination} circula, pero puede haber demoras."
                    )
                else:
                    max_severity = max(max_severity, Severity.BLOCKED)
                    reasons.append(
                        f"Línea {leg.line} limitada entre {st_a} y {st_b} "
                        f"(no llega a cubrir {leg.origin} ↔ {leg.destination})."
                    )
            else:
                max_severity = max(max_severity, Severity.WARNING)
                reasons.append(f"Línea {leg.line} con servicio limitado: «{clause}»")

        # 3. Cierre de estaciones o trenes que no se detienen
        if any(kw in norm for kw in CLOSURE_KEYWORDS):
            matched_known_rule = True
            mentioned = find_mentioned_stations(leg.line, clause)
            if mentioned:
                crit = [st for st in mentioned if st in leg.critical_stations]
                inter = [st for st in mentioned if st in leg.intermediate_stations]
                outside = [st for st in mentioned if st not in leg.segment_stations]

                if crit:
                    max_severity = max(max_severity, Severity.BLOCKED)
                    for st in crit:
                        if st not in closed_critical:
                            closed_critical.append(st)
                    est_str = ", ".join(crit)
                    reasons.append(f"Estación clave cerrada en Línea {leg.line}: {est_str}.")
                if inter:
                    max_severity = max(max_severity, Severity.INFO)
                    est_str = ", ".join(inter)
                    reasons.append(
                        f"Estación intermedia cerrada en Línea {leg.line} ({est_str}): "
                        "el subte pasa sin detenerse pero llegás igual."
                    )
                if outside and not crit and not inter:
                    est_str = ", ".join(outside)
                    ignored_notes.append(
                        f"Línea {leg.line}: {est_str} cerrada(s), fuera de tu tramo ({leg.origin} ↔ {leg.destination})."
                    )
            else:
                max_severity = max(max_severity, Severity.WARNING)
                reasons.append(f"Alerta de cierre en Línea {leg.line}: «{clause}»")

        # 4. Demoras / frecuencia reducida
        if any(kw in norm for kw in DELAY_KEYWORDS):
            matched_known_rule = True
            max_severity = max(max_severity, Severity.WARNING)
            reasons.append(f"Demoras en Línea {leg.line}: «{clause}»")

        # 5. Red de seguridad ante frases nuevas o imprevistas
        if not matched_known_rule:
            max_severity = max(max_severity, Severity.WARNING)
            reasons.append(f"Novedad en Línea {leg.line}: «{clause}»")

    return LegEvaluation(
        leg=leg,
        raw_status=clean_raw,
        severity=max_severity,
        reasons=reasons,
        ignored_notes=ignored_notes,
        closed_critical=closed_critical,
    )


def evaluate_route(route: CommuteRoute, line_statuses: dict[str, str]) -> RouteEvaluation:
    """Evalúa una ruta completa combinando sus dos tramos."""
    leg_evals = [evaluate_leg(leg, line_statuses.get(leg.line, "Servicio normal")) for leg in route.legs]
    overall = max((le.severity for le in leg_evals), default=Severity.OK)

    all_reasons = [r for le in leg_evals for r in le.reasons]
    if overall == Severity.OK:
        headline = f"✅ {route.short_name}: disponible con normalidad"
    elif overall == Severity.INFO:
        headline = f"🟢 {route.short_name}: disponible ({'; '.join(all_reasons)})"
    elif overall == Severity.WARNING:
        headline = f"⚠️ {route.short_name}: disponible pero con demoras/alerta"
    else:
        headline = f"🚫 {route.short_name}: NO disponible ({'; '.join(all_reasons)})"

    return RouteEvaluation(route=route, severity=overall, legs=leg_evals, headline=headline)


DEFAULT_ORIGIN_CORNER = "Av. Luis María Campos y Av. Federico Lacroze"


def analyze_commute(
    line_statuses: dict[str, str],
    source: str = "GCBA",
    updated_at: str = "",
    origin_corner: str = DEFAULT_ORIGIN_CORNER,
) -> CommuteReport:
    """Analiza el estado actual del Subte y recomienda el mejor camino Olleros ↔ UADE."""
    eval_c = evaluate_route(ROUTE_C, line_statuses)
    eval_e = evaluate_route(ROUTE_E, line_statuses)

    # Lógica de decisión priorizando Ruta C (la preferida del usuario) si está en igualdad o normal
    if eval_c.is_usable and (eval_c.severity <= eval_e.severity or not eval_e.is_usable):
        rec_key = "ruta_c"
        if eval_c.severity == Severity.WARNING:
            rec_text = (
                "Podés ir por tu ruta habitual (Línea D hasta 9 de Julio + Línea C a Independencia), "
                "pero salí con unos minutos extra por demoras."
            )
        else:
            rec_text = (
                "Viajá por tu ruta habitual: Línea D (Olleros ↔ 9 de Julio) + "
                "Línea C (Diagonal Norte ↔ Independencia)."
            )
    elif eval_e.is_usable:
        rec_key = "ruta_e"
        if eval_e.severity == Severity.WARNING:
            rec_text = (
                "Usá la ruta alternativa por Línea E (Línea D Olleros ↔ Catedral + "
                "Línea E Bolívar ↔ Independencia), con precaución por demoras."
            )
        else:
            rec_text = (
                "Usá la ruta alternativa: Línea D (Olleros ↔ Catedral) + "
                "Línea E (Bolívar ↔ Independencia)."
            )
    else:
        rec_key = "alternativa_superficie"
        d_leg_9jul = evaluate_leg(ROUTE_C.legs[0], line_statuses.get("D", "Servicio normal"))
        c_status_norm = normalize_text(line_statuses.get("C", ""))
        corner_norm = normalize_text(origin_corner)
        # Caso especial útil: Línea D anda pero C y E tienen problemas en Independencia
        if d_leg_9jul.severity < Severity.BLOCKED:
            if "independencia" in c_status_norm and "interrump" not in c_status_norm:
                rec_text = (
                    "⚠️ Ni Independencia (C) ni la combinación por Línea E están disponibles. "
                    "Alternativa rápida: tomá Línea D hasta 9 de Julio y combiná con Línea C hasta "
                    "Moreno (a 3 cuadras de UADE) o Metrobús 9 de Julio (59 / 67 / 100 / 17)."
                )
            else:
                rec_text = (
                    "⚠️ Combinaciones C y E afectadas, pero Línea D funciona hasta 9 de Julio. "
                    "Desde el Obelisco podés bajar en 9 de Julio y tomar el Metrobús hacia el sur "
                    "(59, 67, 100, 17; ~5 min hasta Av. Independencia) o caminar 10 cuadras por Lima."
                )
        elif "luis maria campos" in corner_norm and "lacroze" in corner_norm:
            rec_text = (
                "🚨 Ambas rutas de Subte están afectadas (incluyendo Línea D). "
                "Alternativa directa desde Luis María Campos y Lacroze (ida y vuelta): "
                "colectivo 59 (te deja en Metrobús 9 de Julio e Independencia, frente a UADE) "
                "o colectivo 60 ramal Constitución (pasa por Salta e Independencia, atrás de UADE)."
            )
        else:
            rec_text = (
                f"🚨 Ambas rutas de Subte están afectadas (incluyendo Línea D). "
                f"Salí directamente en colectivo desde {origin_corner} hacia Metrobús 9 de Julio e Independencia (UADE)."
            )

    # Firma determinística de lo que realmente impacta al usuario (evita alertas repetidas o ruido externo)
    sig_payload = "|".join(
        [
            rec_key,
            f"C:{int(eval_c.severity)}:{';'.join(r for l in eval_c.legs for r in l.reasons)}",
            f"E:{int(eval_e.severity)}:{';'.join(r for l in eval_e.legs for r in l.reasons)}",
        ]
    )
    signature = hashlib.sha256(sig_payload.encode("utf-8")).hexdigest()[:16]

    return CommuteReport(
        line_statuses=dict(line_statuses),
        source=source,
        updated_at=updated_at,
        route_c=eval_c,
        route_e=eval_e,
        recommended_key=rec_key,
        recommendation_text=rec_text,
        signature=signature,
    )


@dataclass
class AlertDecision:
    """Indica si corresponde enviar una notificación por cambio de estado y qué tipo."""

    should_notify: bool
    kind: str  # "none", "reopened_c", "incident", "recovered"
    title: str


def detect_transition(previous_state: dict, report: CommuteReport, notify_on_recovery: bool = True) -> AlertDecision:
    """Compara el estado previo guardado con el nuevo reporte para decidir si alertar."""
    if not previous_state.get("initialized"):
        # En la primera corrida inicializamos la base sin disparar falsa transición,
        # salvo que haya un problema inesperado más allá del cierre ya conocido de Independencia C.
        # Igual mandaremos mensaje de bienvenida si se corre con --init-notify.
        return AlertDecision(should_notify=False, kind="none", title="Estado inicial registrado")

    prev_sig = previous_state.get("route_signature")
    if prev_sig == report.signature:
        return AlertDecision(should_notify=False, kind="none", title="Sin cambios en tus tramos")

    prev_c = previous_state.get("route_c_status")
    prev_e = previous_state.get("route_e_status")
    curr_c = int(report.route_c.severity)
    curr_e = int(report.route_e.severity)

    # Caso estrella: ¡Reabrió Independencia en la Línea C!
    if prev_c == int(Severity.BLOCKED) and curr_c < int(Severity.BLOCKED):
        if notify_on_recovery:
            return AlertDecision(
                should_notify=True,
                kind="reopened_c",
                title="🎉 ¡Habilitada tu Ruta Habitual (Línea C)!",
            )
        return AlertDecision(should_notify=False, kind="none", title="Recuperación silenciada")

    # Si Ruta C seguía bloqueada antes y ahora, y Ruta E no sufrió ningún cambio, evitamos ruido
    prev_e_reasons = previous_state.get("route_e_reasons", "")
    curr_e_reasons = ";".join(r for l in report.route_e.legs for r in l.reasons)
    if (
        prev_c == int(Severity.BLOCKED)
        and curr_c == int(Severity.BLOCKED)
        and prev_e == curr_e
        and prev_e_reasons == curr_e_reasons
    ):
        return AlertDecision(
            should_notify=False,
            kind="none",
            title="Ruta C continúa cerrada; tu Ruta E sigue igual",
        )

    # Empeoró alguna de tus rutas o cambió la ruta recomendada por un problema
    worsened_c = prev_c is not None and curr_c > prev_c
    worsened_e = prev_e is not None and curr_e > prev_e
    both_blocked = curr_c == int(Severity.BLOCKED) and curr_e == int(Severity.BLOCKED)

    if both_blocked:
        return AlertDecision(
            should_notify=True,
            kind="incident",
            title="🚨 ¡Atención! Tus dos rutas de Subte a UADE están afectadas",
        )

    if worsened_c or worsened_e:
        if curr_c == int(Severity.BLOCKED) and worsened_e:
            return AlertDecision(
                should_notify=True,
                kind="incident",
                title="⚠️ ¡Alerta en tu ruta activa a UADE (Línea D / Línea E)!",
            )
        return AlertDecision(
            should_notify=True,
            kind="incident",
            title="⚠️ Novedad que afecta tu viaje en Subte",
        )

    # Mejoró el servicio (ej. se fueron las demoras en la D o reabrió la E)
    if notify_on_recovery and ((prev_e is not None and curr_e < prev_e) or (prev_c is not None and curr_c < prev_c)):
        return AlertDecision(
            should_notify=True,
            kind="recovered",
            title="✅ Se normalizó el servicio en tu recorrido",
        )

    # Cambió el detalle del motivo dentro de una ruta activa con advertencia
    return AlertDecision(
        should_notify=True,
        kind="incident",
        title="🔔 Actualización del estado de tu Subte",
    )


# ========================================================================
# Módulo: scraper.py
# ========================================================================
"""Obtención del estado en tiempo real del Subte (Web oficial GCBA + API Transporte opcional)."""



AR_TZ = ZoneInfo("America/Argentina/Buenos_Aires")

GCBA_HOME_URL = "https://buenosaires.gob.ar/"
GCBA_API_URLS = (
    "https://apitransporte.buenosaires.gob.ar/subtes/serviceAlerts",
    "https://datosabiertos-transporte-apis.buenosaires.gob.ar/subtes/serviceAlerts",
)

SUBTE_LINES = ("A", "B", "C", "D", "E", "H")

# Cabeceras habituales que aparecen debajo del nombre de línea en buenosaires.gob.ar
TERMINAL_DESCRIPTIONS = (
    "plaza de mayo - san pedrito",
    "j.m. rosas - l.n. alem",
    "juan manuel de rosas - leandro n. alem",
    "constitución - retiro",
    "constitucion - retiro",
    "congreso de tucumán - catedral",
    "congreso de tucuman - catedral",
    "retiro - plaza de los virreyes",
    "hospitales - facultad de derecho",
    "int. saguier",
)


@dataclass
class SubteStatusSnapshot:
    """Foto del estado de las líneas de Subte en un instante."""

    lines: dict[str, str]
    source: str
    updated_at: str


def _clean_status_line(raw: str) -> str:
    """Limpia nombres de íconos Material Icons ('check_circle', 'warning', etc.) y espacios."""
    cleaned = re.sub(
        r"^(?:check_circle|warning_amber|warning|error_outline|error|info|lens|circle)\s*",
        "",
        raw.strip(),
        flags=re.IGNORECASE,
    )
    return " ".join(cleaned.split())


def parse_gcba_rendered_text(text: str) -> tuple[dict[str, str], str]:
    """
    Extrae el estado de cada línea a partir del texto visible de buenosaires.gob.ar.
    Funciona con la estructura actual de 'Estado del subte BA'.
    """
    lines_out: dict[str, str] = {}
    updated_at = ""

    match_update = re.search(
        r"[ÚU]ltima actualizaci[óo]n:\s*([0-9]{1,2}/[0-9]{1,2}/[0-9]{4}\s+[0-9]{1,2}:[0-9]{2}(?::[0-9]{2})?)",
        text,
        flags=re.IGNORECASE,
    )
    if match_update:
        updated_at = match_update.group(1).strip()

    raw_lines = [ln.strip() for ln in text.splitlines() if ln.strip()]

    for idx, ln in enumerate(raw_lines):
        m = re.match(r"^L[íi]nea\s+([ABCDEH])$", ln, flags=re.IGNORECASE)
        if not m:
            continue
        letter = m.group(1).upper()
        if letter in lines_out:
            continue

        # Buscamos en las próximas líneas el estado (saltando la línea de cabeceras)
        for offset in range(1, 5):
            if idx + offset >= len(raw_lines):
                break
            candidate = raw_lines[idx + offset]
            cand_lower = candidate.lower()

            # Si es la letra suelta de la siguiente tarjeta o el título de otra línea, frenamos
            if re.match(r"^[ABCDEHP]$", candidate) or re.match(
                r"^(?:L[íi]nea\s+[ABCDEH]|Premetro)$", candidate, flags=re.I
            ):
                break

            # Saltamos la descripción fija de cabeceras (ej. "Constitución - Retiro")
            if any(term in cand_lower for term in TERMINAL_DESCRIPTIONS):
                continue

            status_clean = _clean_status_line(candidate)
            if status_clean:
                lines_out[letter] = status_clean
                break

    return lines_out, updated_at


def _extract_translation_text(field_obj: dict | None) -> str:
    """Extrae texto en español (o primer idioma disponible) de un TranslatedString GTFS-RT."""
    if not isinstance(field_obj, dict):
        return ""
    translations = field_obj.get("translation") or []
    if isinstance(translations, list):
        for item in translations:
            if isinstance(item, dict) and str(item.get("language", "")).lower().startswith("es"):
                return str(item.get("text", "")).strip()
        for item in translations:
            if isinstance(item, dict) and item.get("text"):
                return str(item["text"]).strip()
    return ""


def parse_gcba_gtfs_json(payload: dict) -> SubteStatusSnapshot:
    """Convierte la respuesta JSON de /subtes/serviceAlerts (GTFS-RT) al mapa por línea."""
    alerts_by_line: dict[str, list[str]] = {ln: [] for ln in SUBTE_LINES}

    header_ts = (payload.get("header") or {}).get("timestamp")
    if header_ts:
        try:
            dt = datetime.fromtimestamp(int(header_ts), tz=AR_TZ)
            updated_str = dt.strftime("%d/%m/%Y %H:%M:%S")
        except (ValueError, TypeError, OSError):
            updated_str = datetime.now(AR_TZ).strftime("%d/%m/%Y %H:%M:%S")
    else:
        updated_str = datetime.now(AR_TZ).strftime("%d/%m/%Y %H:%M:%S")

    entities = payload.get("entity") or []
    for ent in entities:
        if not isinstance(ent, dict):
            continue
        alert = ent.get("alert") or ent
        header_txt = _extract_translation_text(alert.get("header_text"))
        desc_txt = _extract_translation_text(alert.get("description_text"))
        combined = " - ".join(p for p in (header_txt, desc_txt) if p).strip()
        if not combined:
            continue

        informed = alert.get("informed_entity") or []
        matched_lines: set[str] = set()
        for inf in informed:
            if not isinstance(inf, dict):
                continue
            route_id = str(inf.get("route_id", "")).strip()
            m = re.search(r"(?:Linea|L[íi]nea)?\s*([ABCDEH])$", route_id, flags=re.I)
            if m:
                matched_lines.add(m.group(1).upper())

        # Si informed_entity vino vacío, intentamos deducir la línea del texto
        if not matched_lines:
            for m in re.finditer(r"L[íi]nea\s+([ABCDEH])\b", combined, flags=re.I):
                matched_lines.add(m.group(1).upper())

        for ln in matched_lines:
            if combined not in alerts_by_line[ln]:
                alerts_by_line[ln].append(combined)

    lines_status: dict[str, str] = {}
    for ln in SUBTE_LINES:
        if alerts_by_line[ln]:
            lines_status[ln] = " | ".join(alerts_by_line[ln])
        else:
            lines_status[ln] = "Servicio normal"

    return SubteStatusSnapshot(
        lines=lines_status,
        source="API Transporte GCBA",
        updated_at=updated_str,
    )


def fetch_from_gcba_api(client_id: str, client_secret: str, timeout: int = 15) -> SubteStatusSnapshot:
    """Consulta la API oficial de Transporte del GCBA (requiere credenciales gratuitas)."""
    params = urllib.parse.urlencode(
        {
            "json": "1",
            "client_id": client_id,
            "client_secret": client_secret,
        }
    )
    last_err: Exception | None = None
    for base_url in GCBA_API_URLS:
        url = f"{base_url}?{params}"
        req = urllib.request.Request(
            url,
            headers={
                "Accept": "application/json",
                "User-Agent": "SubteUADEBot/1.0",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                raw = resp.read().decode("utf-8", errors="replace")
                data = json.loads(raw)
                return parse_gcba_gtfs_json(data)
        except Exception as exc:  # noqa: BLE001
            last_err = exc

    raise RuntimeError(f"No se pudo consultar la API Transporte GCBA: {last_err}")


def fetch_from_gcba_web_playwright(timeout_ms: int = 35000) -> SubteStatusSnapshot:
    """
    Obtiene el estado en vivo desde https://buenosaires.gob.ar/ sin necesidad de API keys,
    renderizando el widget oficial 'Estado del subte BA' con Playwright Chromium.
    """
    from playwright.sync_api import sync_playwright

    with sync_playwright() as p:
        launch_args = ["--no-sandbox", "--disable-dev-shm-usage"]
        try:
            browser = p.chromium.launch(channel="chrome", headless=True, args=launch_args)
        except Exception:  # noqa: BLE001
            browser = p.chromium.launch(headless=True, args=launch_args)
        try:
            context = browser.new_context(
                locale="es-AR",
                timezone_id="America/Argentina/Buenos_Aires",
                user_agent=(
                    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
                ),
            )
            page = context.new_page()
            # Bloqueamos imágenes, fuentes y videos pesados para que cargue el triple de rápido
            page.route(
                "**/*",
                lambda route: route.abort()
                if route.request.resource_type in {"image", "media", "font"}
                else route.continue_(),
            )
            page.goto(GCBA_HOME_URL, wait_until="domcontentloaded", timeout=timeout_ms)
            page.wait_for_function(
                """() => {
                    const txt = document.body ? document.body.innerText : '';
                    return txt.includes('Línea C') && txt.includes('Línea D') && txt.includes('Línea E');
                }""",
                timeout=timeout_ms,
            )
            body_text = page.inner_text("body")
        finally:
            browser.close()

    parsed_lines, updated_at = parse_gcba_rendered_text(body_text)
    missing = [ln for ln in ("C", "D", "E") if ln not in parsed_lines]
    if missing:
        raise RuntimeError(
            f"No se encontraron las líneas {', '.join(missing)} al leer buenosaires.gob.ar"
        )

    if not updated_at:
        updated_at = datetime.now(AR_TZ).strftime("%d/%m/%Y %H:%M:%S")

    return SubteStatusSnapshot(
        lines=parsed_lines,
        source="buenosaires.gob.ar (Estado del Subte BA)",
        updated_at=updated_at,
    )


def fetch_subte_status() -> SubteStatusSnapshot:
    """
    Intenta primero la API oficial GCBA si hay credenciales configuradas;
    si no están (o si la API falla), usa automáticamente la web oficial buenosaires.gob.ar.
    """
    client_id = os.getenv("GCBA_CLIENT_ID", "").strip()
    client_secret = os.getenv("GCBA_CLIENT_SECRET", "").strip()

    if client_id and client_secret:
        try:
            return fetch_from_gcba_api(client_id, client_secret)
        except Exception as api_err:  # noqa: BLE001
            print(f"[WARN] Falló API GCBA ({api_err}), usando fallback web buenosaires.gob.ar...")

    return fetch_from_gcba_web_playwright()


# ========================================================================
# Módulo: telegram_bot.py
# ========================================================================
"""Cliente de Telegram, formato de mensajes y comandos para cambiar días/horarios sin tocar código."""




# Teclado rápido con botones en Telegram para no tener que memorizar comandos
MAIN_REPLY_KEYBOARD = {
    "keyboard": [
        [{"text": "🚇 Estado ahora"}, {"text": "⚙️ Mi configuración"}],
        [{"text": "📅 Cambiar días/turno"}, {"text": "❓ Ayuda"}],
        [{"text": "🏖️ Modo vacaciones"}, {"text": "▶️ Activar alertas"}],
    ],
    "resize_keyboard": True,
    "is_persistent": True,
}


def _severity_badge(sev: Severity) -> str:
    if sev == Severity.OK:
        return "🟢 Normal"
    if sev == Severity.INFO:
        return "🟢 Operativa (estación intermedia sin parada)"
    if sev == Severity.WARNING:
        return "🟡 Con demoras / precaución"
    return "🔴 No disponible"


def format_commute_message(
    report: CommuteReport,
    title: str,
    direction: str | None = None,
    now_dt: datetime | None = None,
) -> str:
    """Construye un mensaje HTML claro y directo para Telegram."""
    now_dt = now_dt or datetime.now(AR_TZ)
    lines: list[str] = [f"<b>{html.escape(title)}</b>"]

    if direction == "ida":
        lines.append("🎒 <i>Reporte antes de salir hacia UADE (Olleros → Independencia)</i>")
    elif direction == "vuelta":
        lines.append("🏠 <i>Reporte para volver de UADE (Independencia → Olleros)</i>")

    lines.append("")
    # Recomendación principal bien visible arriba de todo
    if report.recommended_key == "ruta_c":
        lines.append("👉 <b>Ruta recomendada: RUTA C (Habitual)</b>")
        if direction == "vuelta":
            lines.append(f"   {html.escape(report.route_c.route.summary_vuelta)}")
        else:
            lines.append(f"   {html.escape(report.route_c.route.summary_ida)}")
    elif report.recommended_key == "ruta_e":
        lines.append("👉 <b>Ruta recomendada: RUTA E (por Catedral / Bolívar)</b>")
        if direction == "vuelta":
            lines.append(f"   {html.escape(report.route_e.route.summary_vuelta)}")
        else:
            lines.append(f"   {html.escape(report.route_e.route.summary_ida)}")
    else:
        lines.append("👉 <b>Ruta recomendada: Alternativa por superficie / combinación</b>")

    lines.append(f"💡 {html.escape(report.recommendation_text)}")
    lines.append("")

    # Resumen de ambas rutas
    lines.append("<b>Estado de tus opciones:</b>")
    lines.append(f"• <b>D + C (Diag. Norte):</b> {_severity_badge(report.route_c.severity)}")
    for leg_eval in report.route_c.legs:
        for reason in leg_eval.reasons:
            lines.append(f"   └ {html.escape(reason)}")

    lines.append(f"• <b>D + E (Bolívar):</b> {_severity_badge(report.route_e.severity)}")
    for leg_eval in report.route_e.legs:
        for reason in leg_eval.reasons:
            lines.append(f"   └ {html.escape(reason)}")

    # Notas aclaratorias tranquilizadoras (ej. obras en Entre Ríos/Urquiza que NO afectan)
    ignored = []
    for r_eval in (report.route_c, report.route_e):
        for leg_eval in r_eval.legs:
            for note in leg_eval.ignored_notes:
                if note not in ignored:
                    ignored.append(note)
    if ignored:
        lines.append("")
        lines.append("<i>ℹ️ Cierres que NO afectan tu tramo:</i>")
        for note in ignored:
            lines.append(f"<i>• {html.escape(note)}</i>")

    # Estado crudo oficial de D, C y E
    lines.append("")
    lines.append("<b>Parte oficial Subte BA:</b>")
    for ln in ("D", "C", "E"):
        raw = report.line_statuses.get(ln, "Sin datos")
        icon = "✅" if normalize_text(raw).startswith("servicio normal") else "⚠️"
        lines.append(f"{icon} <b>Línea {ln}:</b> {html.escape(raw)}")

    # Tip nocturno de último tren cuando vuelve de UADE de noche (>= 20:30 hs)
    if direction == "vuelta" or now_dt.hour >= 20:
        is_saturday = now_dt.weekday() == 5
        last_d = "00:01" if is_saturday else "23:32"
        lines.append("")
        lines.append(
            f"🌙 <i>Dato nocturno: el último tren de Línea D desde Catedral hacia Olleros/Congreso "
            f"sale a las <b>{last_d} hs</b>.</i>"
        )

    if report.updated_at:
        lines.append("")
        lines.append(f"🕒 <i>Actualizado: {html.escape(report.updated_at)} ({html.escape(report.source)})</i>")

    return "\n".join(lines)


def format_config_message(config: dict) -> str:
    """Muestra la configuración actual de cursada de forma amigable."""
    enabled = config.get("enabled", True)
    status_str = "🟢 Activas" if enabled else "🏖️ Pausadas (Modo vacaciones)"
    days = [DAY_NAMES.get(d, d) for d in config.get("active_days", [])]
    days_str = ", ".join(days) if days else "Ninguno"
    window = config.get("alert_window") or {}
    sched = config.get("scheduled_reports") or {}
    sched_enabled = sched.get("enabled", True)

    sched_str = (
        f"Ida <b>{sched.get('ida', '17:30')}</b> hs | Vuelta <b>{sched.get('vuelta', '21:45')}</b> hs"
        if sched_enabled
        else "Desactivados"
    )

    origin_corner = str(
        config.get("origin_corner", "Av. Luis María Campos y Av. Federico Lacroze")
    )

    return (
        "⚙️ <b>Tu configuración actual (Subte UADE)</b>\n\n"
        f"• <b>Alertas automáticas:</b> {status_str}\n"
        f"• <b>Esquina de salida (plan B):</b> {html.escape(origin_corner)}\n"
        f"• <b>Días de cursada:</b> {html.escape(days_str)}\n"
        f"• <b>Turno base:</b> {html.escape(str(config.get('turno', 'noche')).capitalize())}\n"
        f"• <b>Horario activo de alertas:</b> {window.get('start', '16:30')} a {window.get('end', '23:30')} hs\n"
        f"• <b>Reportes fijos antes de salir:</b> {sched_str}\n\n"
        "<i>¿Cambió el cuatrimestre? Podés modificar todo desde acá sin tocar código:</i>\n"
        "• <code>/dias lun mie vie</code> (cambia tus días)\n"
        "• <code>/turno manana</code> | <code>/turno tarde</code> | <code>/turno noche</code>\n"
        "• <code>/salida 17:30 21:45</code> (hora reporte ida y vuelta)\n"
        "• <code>/salida off</code> (desactiva el reporte fijo)\n"
        "• <code>/ventana 16:30 23:30</code> (franja horaria de alertas)\n"
        "• <code>/esquina Luis María Campos y Lacroze</code> (cambia tu esquina plan B)\n"
        "• <code>/vacaciones</code> (pausa todo hasta que mandes <code>/activar</code>)"
    )


def format_help_message() -> str:
    """Mensaje de ayuda con todos los comandos disponibles."""
    return (
        "🚇 <b>Bot Subte Olleros ↔ UADE</b>\n\n"
        "Monitoreo tus dos rutas entre <b>Olleros</b> e <b>Independencia (UADE)</b>:\n"
        "1️⃣ <b>Habitual:</b> Línea D (Olleros ↔ 9 de Julio) + Línea C (Diag. Norte ↔ Independencia)\n"
        "2️⃣ <b>Alternativa:</b> Línea D (Olleros ↔ Catedral) + Línea E (Bolívar ↔ Independencia)\n\n"
        "<b>Comandos disponibles:</b>\n"
        "• /estado — Consulta ahora mismo cómo están las líneas y qué ruta conviene\n"
        "• /config — Ver tus días y horarios configurados\n"
        "• <code>/dias mar mie jue vie</code> — Elegir qué días cursás (lun, mar, mie, jue, vie, sab)\n"
        "• <code>/turno noche</code> — Ajustar horarios rápido (<code>manana</code>, <code>tarde</code> o <code>noche</code>)\n"
        "• <code>/salida 17:30 21:45</code> — Cambiar hora de los avisos antes de salir (o <code>/salida off</code>)\n"
        "• <code>/ventana 16:30 23:30</code> — Cambiar en qué horario pueden sonar alertas\n"
        "• /vacaciones — Pausar alertas durante receso/vacaciones\n"
        "• /activar — Volver a activar las alertas"
    )


class TelegramClient:
    """Cliente liviano para la API HTTP de Telegram Bot (sin dependencias externas)."""

    def __init__(self, token: str, allowed_chat_id: str | int | None = None, timeout: int = 15):
        self.token = token.strip()
        self.allowed_chat_id = str(allowed_chat_id).strip() if allowed_chat_id else ""
        self.timeout = timeout
        self.base_url = f"https://api.telegram.org/bot{self.token}"

    def _api_call(self, method: str, payload: dict | None = None) -> dict:
        url = f"{self.base_url}/{method}"
        data = None
        headers = {"Accept": "application/json"}
        if payload is not None:
            data = json.dumps(payload).encode("utf-8")
            headers["Content-Type"] = "application/json; charset=utf-8"

        req = urllib.request.Request(url, data=data, headers=headers, method="POST" if data else "GET")
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            parsed = json.loads(raw)
            if not parsed.get("ok"):
                raise RuntimeError(f"Telegram API error ({method}): {parsed}")
            return parsed

    def send_message(self, text: str, chat_id: str | int | None = None, with_keyboard: bool = True) -> dict:
        target = str(chat_id or self.allowed_chat_id).strip()
        if not target:
            raise ValueError("Falta TELEGRAM_CHAT_ID para enviar el mensaje.")
        payload: dict[str, object] = {
            "chat_id": target,
            "text": text,
            "parse_mode": "HTML",
            "disable_web_page_preview": True,
        }
        if with_keyboard:
            payload["reply_markup"] = MAIN_REPLY_KEYBOARD
        return self._api_call("sendMessage", payload)

    def get_updates(self, offset: int = 0, poll_timeout: int = 0) -> list[dict]:
        params: dict[str, object] = {"timeout": poll_timeout, "allowed_updates": ["message"]}
        if offset > 0:
            params["offset"] = offset
        res = self._api_call("getUpdates", params)
        return res.get("result") or []


def handle_user_command(
    raw_text: str,
    config: dict,
    get_report_fn: Callable[[], CommuteReport],
) -> tuple[str, bool]:
    """
    Procesa un comando o botón enviado por el usuario en Telegram.
    Devuelve (respuesta_html, config_modificada_bool).
    """
    txt = raw_text.strip()
    norm = normalize_text(txt)

    # Mapeo de los botones rápidos a comandos equivalentes
    if "estado ahora" in norm or norm in ("/start", "/estado", "estado"):
        report = get_report_fn()
        prefix = (
            "👋 <b>¡Bot Subte UADE conectado!</b>\nTe dejo el estado en vivo ahora mismo:\n\n"
            if norm == "/start"
            else ""
        )
        msg = format_commute_message(report, title="🚇 Estado actual para tu viaje a UADE")
        return prefix + msg, False

    if "mi configuracion" in norm or norm in ("/config", "config"):
        return format_config_message(config), False

    if "cambiar dias" in norm:
        return (
            "📅 <b>Cómo actualizar tus días u horarios para el próximo cuatrimestre:</b>\n\n"
            "• Para elegir qué días cursás, mandá por ejemplo:\n"
            "  <code>/dias lun mie vie</code>\n"
            "  <code>/dias mar mie jue vie</code>\n\n"
            "• Para cambiar de turno de una sola vez:\n"
            "  <code>/turno manana</code>\n"
            "  <code>/turno tarde</code>\n"
            "  <code>/turno noche</code>\n\n"
            "• Para ajustar tus horarios exactos de reporte fijo antes de salir:\n"
            "  <code>/salida 17:30 21:45</code> (o <code>/salida off</code>)\n\n"
            "• Para cambiar el rango horario en el que recibís alertas:\n"
            "  <code>/ventana 16:30 23:30</code>",
            False,
        )

    if "ayuda" in norm or norm in ("/ayuda", "/help"):
        return format_help_message(), False

    if "modo vacaciones" in norm or norm in ("/vacaciones", "/pausar", "/silenciar"):
        config["enabled"] = False
        return (
            "🏖️ <b>Modo vacaciones activado.</b>\n"
            "Pausé las alertas y reportes automáticos para no molestarte en el receso.\n\n"
            "Seguís pudiendo consultar /estado cuando quieras, y cuando arranque la cursada "
            "tocá <b>▶️ Activar alertas</b> o mandá /activar.",
            True,
        )

    if "activar alertas" in norm or norm in ("/activar", "/reanudar"):
        config["enabled"] = True
        return (
            "▶️ <b>¡Alertas automáticas activadas!</b>\n\n" + format_config_message(config),
            True,
        )

    # /dias lun mar mie...
    if norm.startswith("/dias"):
        tokens = re.split(r"[\s,;]+", norm)[1:]
        alias_day = {
            "lunes": "lun",
            "lun": "lun",
            "martes": "mar",
            "mar": "mar",
            "miercoles": "mie",
            "mie": "mie",
            "jueves": "jue",
            "jue": "jue",
            "viernes": "vie",
            "vie": "vie",
            "sabado": "sab",
            "sab": "sab",
            "domingo": "dom",
            "dom": "dom",
        }
        chosen: list[str] = []
        invalid: list[str] = []
        for tok in tokens:
            if not tok:
                continue
            mapped = alias_day.get(tok)
            if mapped:
                if mapped not in chosen:
                    chosen.append(mapped)
            else:
                invalid.append(tok)

        if not chosen or invalid:
            return (
                "⚠️ Indicá los días separados por espacio. Ejemplo:\n"
                "<code>/dias mar mie jue vie</code>\n"
                "<i>Valores válidos: lun, mar, mie, jue, vie, sab, dom</i>",
                False,
            )

        chosen.sort(key=lambda d: DAY_CODES.index(d))
        config["active_days"] = chosen
        return "✅ <b>Días de cursada actualizados.</b>\n\n" + format_config_message(config), True

    # /turno manana | tarde | noche
    if norm.startswith("/turno"):
        parts = norm.split()
        if len(parts) < 2 or parts[1] not in TURNOS_PRESETS:
            return (
                "⚠️ Elegí uno de los tres turnos:\n"
                "• <code>/turno manana</code>\n"
                "• <code>/turno tarde</code>\n"
                "• <code>/turno noche</code>",
                False,
            )
        preset_key = parts[1]
        preset = TURNOS_PRESETS[preset_key]
        config["turno"] = preset_key
        config["alert_window"] = dict(preset["alert_window"])  # type: ignore[arg-type]
        config["scheduled_reports"] = dict(preset["scheduled_reports"])  # type: ignore[arg-type]
        return (
            f"✅ <b>Turno {html.escape(str(preset['label']))} configurado.</b>\n\n"
            + format_config_message(config),
            True,
        )

    # /salida 17:30 21:45 o /salida off
    if norm.startswith("/salida"):
        parts = norm.split()
        if len(parts) == 2 and parts[1] in ("off", "no", "desactivar"):
            config.setdefault("scheduled_reports", {})["enabled"] = False
            return "✅ <b>Reportes fijos antes de salir desactivados.</b>\nSolo recibirás alertas cuando cambie algo.", True

        if len(parts) == 3:
            try:
                parse_hhmm(parts[1])
                parse_hhmm(parts[2])
            except ValueError as err:
                return f"⚠️ {html.escape(str(err))}", False
            config["scheduled_reports"] = {
                "enabled": True,
                "ida": parts[1],
                "vuelta": parts[2],
            }
            return "✅ <b>Horarios de reporte antes de salir actualizados.</b>\n\n" + format_config_message(config), True

        return (
            "⚠️ Usá <code>/salida HH:MM HH:MM</code> (ida y vuelta) o <code>/salida off</code>.\n"
            "Ejemplo: <code>/salida 17:30 21:45</code>",
            False,
        )

    # /ventana 16:30 23:30
    if norm.startswith("/ventana"):
        parts = norm.split()
        if len(parts) == 3:
            try:
                parse_hhmm(parts[1])
                parse_hhmm(parts[2])
            except ValueError as err:
                return f"⚠️ {html.escape(str(err))}", False
            config["alert_window"] = {"start": parts[1], "end": parts[2]}
            return "✅ <b>Franja horaria de alertas actualizada.</b>\n\n" + format_config_message(config), True

        return (
            "⚠️ Usá <code>/ventana HH:MM HH:MM</code>.\n"
            "Ejemplo: <code>/ventana 16:30 23:30</code>",
            False,
        )

    # /esquina <dirección>
    if norm.startswith("/esquina"):
        raw_arg = txt.partition(" ")[2].strip()
        if not raw_arg:
            return (
                "⚠️ Indicá la esquina después del comando.\n"
                "Ejemplo: <code>/esquina Av. Luis María Campos y Av. Federico Lacroze</code>",
                False,
            )
        config["origin_corner"] = raw_arg
        return "✅ <b>Esquina de salida (plan B) actualizada.</b>\n\n" + format_config_message(config), True

    return (
        "🤔 No reconocí ese comando.\nTocá uno de los botones de abajo o mandá /ayuda para ver las opciones.",
        False,
    )


# ========================================================================
# Ejecución principal
# ========================================================================
"""Punto de entrada principal del Bot de Alertas Subte Olleros ↔ UADE."""




BASE_DIR = Path(__file__).resolve().parent
CONFIG_PATH = BASE_DIR / "data" / "config.json"
STATE_PATH = BASE_DIR / "data" / "state.json"


def load_json(path: Path, default: dict) -> dict:
    if not path.exists():
        return json.loads(json.dumps(default))
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def save_json_if_changed(path: Path, payload: dict) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    if path.exists():
        existing = path.read_text(encoding="utf-8")
        if existing == rendered:
            return False
    path.write_text(rendered, encoding="utf-8")
    return True


def _update_notified_baseline(state: dict, report: CommuteReport, now_ar: datetime) -> None:
    """Guarda en state la última foto que el usuario conoce o que se evaluó en horario hábil."""
    state["initialized"] = True
    state["last_check_iso"] = now_ar.isoformat(timespec="seconds")
    state["recommended_route"] = report.recommended_key
    state["route_c_status"] = int(report.route_c.severity)
    state["route_e_status"] = int(report.route_e.severity)
    state["route_e_reasons"] = ";".join(r for l in report.route_e.legs for r in l.reasons)
    state["route_signature"] = report.signature


def process_telegram_inbox(
    tg: TelegramClient,
    config: dict,
    state: dict,
    get_report_fn,
    poll_timeout: int = 0,
) -> bool:
    """Lee mensajes entrantes en Telegram y responde comandos del usuario."""
    offset = int(state.get("last_update_id", 0)) + 1 if state.get("last_update_id") else 0
    updates = tg.get_updates(offset=offset, poll_timeout=poll_timeout)
    config_changed = False

    for upd in updates:
        upd_id = int(upd.get("update_id", 0))
        if upd_id > int(state.get("last_update_id", 0)):
            state["last_update_id"] = upd_id

        msg = upd.get("message") or {}
        chat = msg.get("chat") or {}
        chat_id = str(chat.get("id", "")).strip()
        text = str(msg.get("text", "")).strip()
        if not chat_id or not text:
            continue

        # Si el usuario todavía no configuró TELEGRAM_CHAT_ID, le ayudamos mostrándoselo
        if not tg.allowed_chat_id:
            tg.send_message(
                f"👋 ¡Hola! Tu <code>TELEGRAM_CHAT_ID</code> es: <code>{chat_id}</code>\n"
                "Guardalo en los Secrets de GitHub para terminar la configuración.",
                chat_id=chat_id,
                with_keyboard=False,
            )
            continue

        # Por seguridad, ignorar mensajes de terceros ajenos al dueño del bot
        if chat_id != tg.allowed_chat_id:
            print(f"[INFO] Ignorando mensaje de chat_id no autorizado: {chat_id}")
            continue

        reply_html, modified = handle_user_command(text, config, get_report_fn)
        if modified:
            config_changed = True
        tg.send_message(reply_html, chat_id=chat_id, with_keyboard=True)

    return config_changed


def run_once(force_report: bool = False) -> None:
    """Ejecuta un ciclo completo (ideal para GitHub Actions o cron)."""
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    if not token:
        raise SystemExit(
            "ERROR: Falta la variable TELEGRAM_BOT_TOKEN. Configurala en GitHub Secrets o en tu entorno."
        )

    config = load_json(CONFIG_PATH, default=DEFAULT_CONFIG)
    state = load_json(STATE_PATH, default={"initialized": False, "last_update_id": 0})
    tg = TelegramClient(token=token, allowed_chat_id=chat_id)
    now_ar = datetime.now(AR_TZ)

    cached_report: CommuteReport | None = None

    def get_report() -> CommuteReport:
        nonlocal cached_report
        if cached_report is None:
            snapshot = fetch_subte_status()
            cached_report = analyze_commute(
                line_statuses=snapshot.lines,
                source=snapshot.source,
                updated_at=snapshot.updated_at,
                origin_corner=str(
                    config.get("origin_corner", "Av. Luis María Campos y Av. Federico Lacroze")
                ),
            )
        return cached_report

    # 1. Procesar cualquier comando que el usuario haya escrito en Telegram
    try:
        process_telegram_inbox(tg, config, state, get_report, poll_timeout=0)
    except Exception as inbox_err:  # noqa: BLE001
        print(f"[WARN] No se pudo revisar bandeja de entrada de Telegram: {inbox_err}")

    if not chat_id:
        save_json_if_changed(CONFIG_PATH, config)
        save_json_if_changed(STATE_PATH, state)
        print("[WARN] Falta TELEGRAM_CHAT_ID. Mandale /start al bot y revisá el mensaje.")
        return

    report = get_report()

    # 2. Primera ejecución histórica: mandar bienvenida con el estado actual en vivo
    if not state.get("initialized"):
        welcome_msg = format_commute_message(
            report,
            title="🎉 ¡Bot Subte UADE activado y monitoreando!",
            now_dt=now_ar,
        )
        tg.send_message(welcome_msg)
        _update_notified_baseline(state, report, now_ar)
        save_json_if_changed(CONFIG_PATH, config)
        save_json_if_changed(STATE_PATH, state)
        print("[OK] Mensaje inicial de activación enviado a Telegram.")
        return

    # 3. Si se pidió reporte manual desde GitHub Actions ("Run workflow" con force_report)
    if force_report:
        msg = format_commute_message(
            report,
            title="🚇 Estado actual de tu viaje a UADE (chequeo manual)",
            now_dt=now_ar,
        )
        tg.send_message(msg)
        _update_notified_baseline(state, report, now_ar)
        save_json_if_changed(CONFIG_PATH, config)
        save_json_if_changed(STATE_PATH, state)
        print("[OK] Reporte manual enviado.")
        return

    # 4. Reportes fijos programados antes de salir (ida / vuelta en días de cursada)
    sent_scheduled = False
    for slot in due_scheduled_reports(now_ar, config, state):
        slot_title = (
            "🎒 Estado del Subte antes de ir a UADE"
            if slot == "ida"
            else "🏠 Estado del Subte antes de volver de UADE"
        )
        msg = format_commute_message(report, title=slot_title, direction=slot, now_dt=now_ar)
        tg.send_message(msg)
        mark_report_sent(now_ar, state, slot)
        _update_notified_baseline(state, report, now_ar)
        sent_scheduled = True
        print(f"[OK] Reporte programado '{slot}' enviado.")

    # 5. Alertas por cambio de estado (solo dentro de días y ventana horaria de cursada)
    if not sent_scheduled and is_within_alert_window(now_ar, config):
        decision = detect_transition(
            previous_state=state,
            report=report,
            notify_on_recovery=bool(config.get("notify_on_recovery", True)),
        )
        if decision.should_notify:
            msg = format_commute_message(report, title=decision.title, now_dt=now_ar)
            tg.send_message(msg)
            print(f"[ALERTA] {decision.kind}: {decision.title}")
        else:
            print(f"[OK] Sin alertas nuevas ({decision.title}).")

        # Actualizamos la base notificada porque estamos dentro de la ventana activa
        _update_notified_baseline(state, report, now_ar)
    elif not sent_scheduled:
        print(
            f"[SILENCIO] Fuera de horario/día de cursada ({now_ar.strftime('%a %H:%M')} AR). "
            "Se conserva la última referencia para avisar al abrir tu próxima ventana si algo sigue afectado."
        )

    save_json_if_changed(CONFIG_PATH, config)
    save_json_if_changed(STATE_PATH, state)


def run_live_loop(check_interval_sec: int = 300) -> None:
    """Modo continuo opcional (por si algún día se corre en PC o servidor 24/7)."""
    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    if not token:
        raise SystemExit("ERROR: Falta TELEGRAM_BOT_TOKEN.")

    tg = TelegramClient(token=token, allowed_chat_id=chat_id, timeout=35)
    last_subte_check = 0.0
    print("🚇 Bot Subte UADE corriendo en vivo (Ctrl+C para detener)...")

    while True:
        try:
            now_ts = time.time()
            config = load_json(CONFIG_PATH, default=DEFAULT_CONFIG)
            state = load_json(STATE_PATH, default={"initialized": False, "last_update_id": 0})

            def get_live_report() -> CommuteReport:
                snap = fetch_subte_status()
                return analyze_commute(
                    snap.lines,
                    source=snap.source,
                    updated_at=snap.updated_at,
                    origin_corner=str(
                        config.get("origin_corner", "Av. Luis María Campos y Av. Federico Lacroze")
                    ),
                )

            process_telegram_inbox(tg, config, state, get_live_report, poll_timeout=20)
            save_json_if_changed(CONFIG_PATH, config)
            save_json_if_changed(STATE_PATH, state)

            if now_ts - last_subte_check >= check_interval_sec:
                run_once(force_report=False)
                last_subte_check = now_ts
        except KeyboardInterrupt:
            print("\nDetenido por el usuario.")
            break
        except Exception as err:  # noqa: BLE001
            print(f"[ERROR] Ciclo en vivo: {err}")
            time.sleep(10)


def run_demo() -> None:
    """Muestra en consola ejemplos reales de cómo analiza hoy tu viaje a UADE."""
    sample_today = {
        "A": "Servicio normal",
        "B": "Estación Medrano cerrada por obras de renovación integral.",
        "C": "Independencia y Lavalle cerradas por obras de renovación integral.",
        "D": "Servicio normal",
        "E": "Entre Ríos y Urquiza cerradas por obras de renovación integral.",
        "H": "Servicio normal",
    }
    rep = analyze_commute(
        sample_today,
        source="Simulación real 25/11/2026",
        updated_at="25/11/2026 17:30:00",
    )
    print("=== DEMO: ESTADO REAL ACTUAL (INDEPENDENCIA C CERRADA) ===")
    print(format_commute_message(rep, title="🎒 Estado del Subte antes de ir a UADE", direction="ida"))


def main() -> None:
    parser = argparse.ArgumentParser(description="Bot de Telegram para Subte Olleros ↔ UADE")
    parser.add_argument(
        "--force-report",
        action="store_true",
        help="Envía un reporte inmediato a Telegram sin importar el día/hora.",
    )
    parser.add_argument(
        "--live",
        action="store_true",
        help="Ejecuta el bot en bucle continuo (para PC o servidor propio).",
    )
    parser.add_argument(
        "--demo",
        action="store_true",
        help="Imprime una demostración local sin conectarse a Telegram.",
    )
    args = parser.parse_args()

    force_env = os.getenv("FORCE_REPORT", "").strip().lower() in ("1", "true", "yes", "si")
    if args.demo:
        run_demo()
    elif args.live:
        run_live_loop()
    else:
        run_once(force_report=args.force_report or force_env)


if __name__ == "__main__":
    sys.exit(main())
