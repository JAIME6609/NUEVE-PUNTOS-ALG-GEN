#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BÚSQUEDA GENÉTICA DE LA CIRCUNFERENCIA DE LOS NUEVE PUNTOS
Implementación completa y comentada de las siete etapas del artículo V8.

DOCUMENTO DE PARTIDA
-------------------
Jaime Aguilar-Ortiz, «Búsqueda genética y verificación exacta de la
circunferencia de los nueve puntos», ARTICULO-01-NUEVE-PUNTOS-V8.docx.
El programa no necesita abrir el Word: contiene las definiciones, los
operadores y los experimentos necesarios para efectuar los cálculos.

QUÉ HACE EL PROGRAMA
-------------------
1. Construye exactamente el triángulo A=(0,0), B=(4,0), C=(1,3), sus centros
   geométricos y las tres familias que forman los nueve puntos.
2. Recalcula las cuentas ilustrativas de la tabla 2 y la figura 3. Son ejemplos
   didácticos independientes de las poblaciones de las corridas aleatorias.
3. Ejecuta las siete etapas del algoritmo genético con los parámetros del
   artículo: 100 posiciones, 16 bits, dos élites y 500 generaciones completas.
4. Repite el experimento con las semillas enteras 0,...,29. Guarda las 501
   poblaciones de cada corrida y sus métricas; un hallazgo temprano de J=0
   nunca interrumpe las generaciones restantes.
5. Certifica cada mejor candidato final con Fraction: comprueba construcciones
   y nueve distancias. Un error decimal pequeño no se convierte en un éxito.
6. Enumera los 65,536 cromosomas y, de forma separada, las 2,300 ternas de la
   rejilla geométrica; ejecuta los cuatro controles alterados del artículo.
7. Exporta tablas CSV, resultados JSON, una explicación TXT y cinco figuras
   calculadas (PNG de 300 dpi y SVG), cuando Matplotlib está disponible.

LAS SIETE ETAPAS EN EL CÓDIGO
----------------------------
    etapa_1_inicializar
    etapa_2_evaluar
    etapa_3_seleccionar
    etapa_4_cruzar
    etapa_5_mutar
    etapa_6_reemplazar
    etapa_7_terminar_y_certificar

POR QUÉ SE DISTINGUEN BÚSQUEDA, VERIFICACIÓN Y DEMOSTRACIÓN
-------------------------------------------------------
El algoritmo recibe los tres puntos medios de lados y R² para evaluar J.
No recibe el centro N como solución que deba insertar en la población.
La geometría exacta se usa después para verificar los candidatos y para
estudiar el certificado. Las identidades de las ecuaciones (8)-(10) se
explican en los comentarios y se comprueban con fracciones. Su comprobación
en un banco finito no sustituye una demostración universal ni una prueba
formal de corrección de todo el software.

REPRODUCIBILIDAD Y RESULTADOS PUBLICADOS
--------------------------------------
El artículo fija random.Random(seed), getrandbits(1), las semillas y los
parámetros, pero no publica todo el orden de llamadas aleatorias ni la API
usada para índices y empates. Aquí se fija un protocolo explícito:
    a) todos los torneos de una generación;
    b) todos sus cruces;
    c) todas las mutaciones, de izquierda a derecha;
    d) reemplazo y evaluación completa.
Se usa sample para los dos índices, choice para todo empate y randrange para
el corte. Las élites se extraen mediante ordenación estable sin reordenar la
población de los torneos. Es una implementación de la metodología publicada,
no una recuperación del archivo fuente original. Los valores del artículo
solo se usan como referencias de comparación. No se modifican semillas,
resultados ni operadores para forzar una tasa de éxito determinada.

El artículo informa 21 comprobaciones auxiliares por triángulo, pero no las
enumera. El bloque geométrico declara las condiciones concretas que implementa
y su carácter de reconstrucción explícita de ese control.

EJECUCIÓN
---------
En Spyder/Anaconda: abrir este archivo y pulsar F5. Los parámetros editables
están en CONFIGURACION_USUARIO. El cálculo principal usa la biblioteca
estándar de Python. Matplotlib se utiliza únicamente para las figuras.

En una terminal:
    python Algoritmo_Genetico_Nueve_Puntos_7_Etapas.py

Ejemplo de ejecución breve para explorar el programa:
    python Algoritmo_Genetico_Nueve_Puntos_7_Etapas.py --corridas 3 --generaciones 20

El modo breve cambia el experimento. El informe identifica esos cambios y
no presenta sus métricas como reproducción de las 30 corridas del artículo.

Si se requieren las figuras y falta Matplotlib:
    python -m pip install matplotlib
O bien ejecutar con --instalar-matplotlib para autorizar esa instalación.
La instalación automática está desactivada por defecto.

La carpeta de salida se crea junto al archivo .py y lleva fecha y hora para
conservar resultados anteriores. --salida permite elegir otra carpeta.
Con --solo-pruebas se ejecutan las autocomprobaciones y se sale.
Con --sin-figuras se ejecuta toda la parte numérica sin Matplotlib.

DOCUMENTACIÓN PRIMARIA DE LAS API UTILIZADAS
------------------------------------------
https://docs.python.org/3.12/library/random.html
https://docs.python.org/3.12/library/fractions.html
https://matplotlib.org/stable/api/_as_gen/matplotlib.pyplot.savefig.html

Compatibilidad prevista: Python 3.10 o posterior. El experimento entregado se
probó con Python 3.12.14, la versión indicada en el artículo. Los metadatos de
cada nueva ejecución registran la versión efectivamente utilizada.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import importlib.util
import json
import math
import platform
import statistics
import subprocess
import sys
import time
from contextlib import ExitStack
from dataclasses import asdict, is_dataclass
from datetime import datetime
from fractions import Fraction
from pathlib import Path


# Esta sección permite usar el programa desde Spyder sin editar las funciones.
# Los valores predeterminados corresponden al experimento descrito en V8.
# Si se cambian, el programa registra la configuración nueva en sus salidas.
CONFIGURACION_USUARIO = {
    "poblacion": 100,
    "generaciones": 500,
    "corridas": 30,
    "primera_semilla": 0,
    "probabilidad_cruce": 0.90,
    "probabilidad_mutacion": 0.01,
    "elites": 2,
    "generar_figuras": True,
    "guardar_poblaciones_completas": True,
    "ejecutar_autocomprobaciones": True,
    "instalar_matplotlib_si_falta": False,
}

# Los vértices definen el experimento; no son una población inicial.
VERTICES_ESTUDIO = ((0, 0), (4, 0), (1, 3))

# El programa contiene más de un bloque porque reproduce las distintas partes
# del artículo. Todos los bloques están incluidos en ESTE archivo; no se
# necesitan módulos locales, fragmentos omitidos ni archivos de datos externos.

"""Geometría racional exacta del artículo V8 sobre la circunferencia de nueve puntos.

Este componente usa únicamente la biblioteca estándar. Puede copiarse al programa
principal como una sección del mismo archivo; no importa módulos del proyecto ni
ejecuta experimentos al importarse. Todas las cantidades geométricas se calculan
con ``Fraction``: las cifras publicadas se utilizan solo para contrastar resultados.

Convenciones importantes
-----------------------
* A, B y C tienen el orden recibido. En el banco se asignan por orden lexicográfico.
* Se conservan las nueve ETIQUETAS aunque coincidan algunas coordenadas.
* Las proyecciones se hacen sobre rectas, no sobre segmentos. No se recorta el
  parámetro de proyección al intervalo [0, 1].
* El residuo general es 4 (distancia² - radio²). Con el radio correcto coincide
  con 4 distancia² - R²; en el control del radio es 4 distancia² - 4R²/3.
* El artículo no enumera sus 21 comprobaciones auxiliares. Aquí se reconstruye
  un conjunto explícito de 21 identidades naturales de las ecuaciones (6)-(10).
  No se afirma que sean las mismas instrucciones del programa original.
* Una batería finita de verificaciones exactas comprueba esta implementación;
  no reemplaza la demostración algebraica general ni una verificación formal.
"""


from dataclasses import asdict, dataclass, is_dataclass
from fractions import Fraction
from itertools import combinations
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, Union


ExactScalar = Union[int, str, Fraction]


def geo_exact_fraction(value: ExactScalar) -> Fraction:
    """Convierte enteros, fracciones o cadenas racionales sin introducir flotantes.

    Una cadena como "0.1" designa exactamente 1/10. Se rechaza un ``float``:
    aceptar su expansión binaria silenciosamente sería contrario al protocolo.
    """
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise TypeError("Se requiere un entero, Fraction o cadena racional exacta.")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("La cantidad no representa un número racional válido.") from error


@dataclass(frozen=True)
class Point:
    """Punto o vector del plano; sus dos coordenadas siempre son Fraction."""

    x: Fraction
    y: Fraction

    def __post_init__(self) -> None:
        object.__setattr__(self, "x", geo_exact_fraction(self.x))
        object.__setattr__(self, "y", geo_exact_fraction(self.y))

    def __add__(self, other: Point) -> Point:
        if not isinstance(other, Point):
            return NotImplemented
        return Point(self.x + other.x, self.y + other.y)

    def __sub__(self, other: Point) -> Point:
        if not isinstance(other, Point):
            return NotImplemented
        return Point(self.x - other.x, self.y - other.y)

    def __neg__(self) -> Point:
        return Point(-self.x, -self.y)

    def __mul__(self, scalar: ExactScalar) -> Point:
        value = geo_exact_fraction(scalar)
        return Point(self.x * value, self.y * value)

    def __rmul__(self, scalar: ExactScalar) -> Point:
        return self * scalar

    def __truediv__(self, scalar: ExactScalar) -> Point:
        value = geo_exact_fraction(scalar)
        if value == 0:
            raise ZeroDivisionError("No se puede dividir un punto por cero.")
        return Point(self.x / value, self.y / value)

    def __iter__(self) -> Iterable[Fraction]:
        return iter((self.x, self.y))

    def as_pair(self) -> Tuple[Fraction, Fraction]:
        return self.x, self.y


PointLike = Union[Point, Tuple[ExactScalar, ExactScalar], Sequence[ExactScalar]]


def geo_as_point(value: PointLike) -> Point:
    """Normaliza un Point o una secuencia de dos coordenadas exactas."""
    if isinstance(value, Point):
        return value
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError("Se requiere un punto o una secuencia de dos coordenadas.")
    if len(value) != 2:
        raise ValueError("Un punto del plano necesita exactamente dos coordenadas.")
    return Point(value[0], value[1])


def geo_dot(left: Point, right: Point) -> Fraction:
    """Producto escalar U·V; expresa normas y condiciones de ortogonalidad."""
    return left.x * right.x + left.y * right.y


def geo_cross(left: Point, right: Point) -> Fraction:
    """Determinante de dos vectores; cero significa dependencia lineal."""
    return left.x * right.y - left.y * right.x


def geo_norm_squared(vector: Point) -> Fraction:
    return geo_dot(vector, vector)


def geo_distance_squared(left: PointLike, right: PointLike) -> Fraction:
    return geo_norm_squared(geo_as_point(left) - geo_as_point(right))


def geo_midpoint(left: PointLike, right: PointLike) -> Point:
    return (geo_as_point(left) + geo_as_point(right)) / 2


def geo_signed_double_area(a: PointLike, b: PointLike, c: PointLike) -> Fraction:
    """Δ de (5), sin valor absoluto: conserva la orientación del triángulo."""
    aa, bb, cc = geo_as_point(a), geo_as_point(b), geo_as_point(c)
    return geo_cross(bb - aa, cc - aa)


@dataclass(frozen=True)
class Triangle:
    """Triángulo racional no degenerado; rechaza duplicados y colinealidad."""

    a: Point
    b: Point
    c: Point

    def __post_init__(self) -> None:
        for name in ("a", "b", "c"):
            object.__setattr__(self, name, geo_as_point(getattr(self, name)))
        if self.delta == 0:
            raise ValueError("Los tres vértices deben ser distintos y no colineales.")

    @property
    def delta(self) -> Fraction:
        return geo_cross(self.b - self.a, self.c - self.a)

    @property
    def vertices(self) -> Tuple[Point, Point, Point]:
        return self.a, self.b, self.c

    @property
    def side_lengths_squared(self) -> Tuple[Fraction, Fraction, Fraction]:
        # Orden BC, CA, AB: corresponde a los subíndices a, b, c.
        return (
            geo_distance_squared(self.b, self.c),
            geo_distance_squared(self.c, self.a),
            geo_distance_squared(self.a, self.b),
        )

    @property
    def triangle_class(self) -> str:
        """Clasificación angular exacta, sin raíces ni tolerancias."""
        small, middle, large = sorted(self.side_lengths_squared)
        difference = small + middle - large
        if difference > 0:
            return "acutangulo"
        if difference == 0:
            return "rectangulo"
        return "obtusangulo"


POINT_LABELS = ("Ma", "Mb", "Mc", "Da", "Db", "Dc", "Ea", "Eb", "Ec")
TRIANGLE_CLASSES = ("acutangulo", "rectangulo", "obtusangulo")
CLASS_LABELS = {
    "acutangulo": "Acutángulos",
    "rectangulo": "Rectángulos",
    "obtusangulo": "Obtusángulos",
}
CONTROL_LABELS = {
    "shifted_center": "Centro desplazado",
    "wrong_radius": "Radio incorrecto",
    "third_feet": "Pies en tercios",
    "third_euler": "Euler en tercios",
}


def geo_project_onto_line(vertex: PointLike, start: PointLike, end: PointLike) -> Point:
    """Proyección (7) sobre la recta start--end, incluso fuera del segmento."""
    vertex, start, end = geo_as_point(vertex), geo_as_point(start), geo_as_point(end)
    direction = end - start
    denominator = geo_norm_squared(direction)
    if denominator == 0:
        raise ValueError("Una recta necesita dos puntos distintos.")
    return start + direction * (geo_dot(vertex - start, direction) / denominator)


@dataclass(frozen=True)
class NinePointGeometry:
    """Construcción de referencia; una configuración alterada no la modifica."""

    triangle: Triangle
    circumcenter: Point
    orthocenter: Point
    center: Point
    circumradius_squared: Fraction
    radius_squared: Fraction
    named_points: Tuple[Tuple[str, Point], ...]
    projection_denominators: Tuple[Fraction, Fraction, Fraction]

    @property
    def points(self) -> Dict[str, Point]:
        # Se devuelve una copia: los controles no pueden contaminar la referencia.
        return dict(self.named_points)

    @property
    def side_midpoints(self) -> Tuple[Point, Point, Point]:
        points = self.points
        return points["Ma"], points["Mb"], points["Mc"]

    @property
    def midpoints(self) -> Dict[str, Point]:
        return {label: point for label, point in self.named_points if label.startswith("M")}

    @property
    def labels(self) -> Tuple[str, ...]:
        return tuple(label for label, _ in self.named_points)

    # Aliases matemáticos para la integración con las etapas del algoritmo.
    @property
    def O(self) -> Point:
        return self.circumcenter

    @property
    def H(self) -> Point:
        return self.orthocenter

    @property
    def N(self) -> Point:
        return self.center

    @property
    def R2(self) -> Fraction:
        return self.circumradius_squared

    @property
    def r2(self) -> Fraction:
        return self.radius_squared


def construct_geometry(
    a: Union[PointLike, Triangle],
    b: Optional[PointLike] = None,
    c: Optional[PointLike] = None,
) -> NinePointGeometry:
    """Calcula O, H, N, R², r² y las nueve posiciones desde tres vértices.

    También acepta un objeto Triangle como único argumento. El sistema de (6)
    se resuelve por determinantes; su determinante es exactamente 4Δ.
    """
    if isinstance(a, Triangle):
        if b is not None or c is not None:
            raise ValueError("Con Triangle no deben proporcionarse otros vértices.")
        triangle = a
    else:
        if b is None or c is None:
            raise ValueError("Deben proporcionarse los tres vértices.")
        triangle = Triangle(geo_as_point(a), geo_as_point(b), geo_as_point(c))
    aa, bb, cc = triangle.vertices
    ba, ca = bb - aa, cc - aa
    m11, m12, m21, m22 = 2 * ba.x, 2 * ba.y, 2 * ca.x, 2 * ca.y
    right1 = geo_norm_squared(bb) - geo_norm_squared(aa)
    right2 = geo_norm_squared(cc) - geo_norm_squared(aa)
    determinant = m11 * m22 - m12 * m21
    circumcenter = Point(
        (right1 * m22 - m12 * right2) / determinant,
        (m11 * right2 - right1 * m21) / determinant,
    )
    circumradius_squared = geo_distance_squared(aa, circumcenter)
    orthocenter = aa + bb + cc - 2 * circumcenter
    center = geo_midpoint(circumcenter, orthocenter)
    named_points = (
        ("Ma", geo_midpoint(bb, cc)),
        ("Mb", geo_midpoint(cc, aa)),
        ("Mc", geo_midpoint(aa, bb)),
        ("Da", geo_project_onto_line(aa, bb, cc)),
        ("Db", geo_project_onto_line(bb, cc, aa)),
        ("Dc", geo_project_onto_line(cc, aa, bb)),
        ("Ea", geo_midpoint(aa, orthocenter)),
        ("Eb", geo_midpoint(bb, orthocenter)),
        ("Ec", geo_midpoint(cc, orthocenter)),
    )
    return NinePointGeometry(
        triangle=triangle,
        circumcenter=circumcenter,
        orthocenter=orthocenter,
        center=center,
        circumradius_squared=circumradius_squared,
        radius_squared=circumradius_squared / 4,
        named_points=named_points,
        projection_denominators=triangle.side_lengths_squared,
    )


def example_geometry() -> NinePointGeometry:
    return construct_geometry((0, 0), (4, 0), (1, 3))


def nine_point_residuals(
    geometry: NinePointGeometry,
    center: Optional[PointLike] = None,
    radius_squared: Optional[ExactScalar] = None,
    points: Optional[Mapping[str, PointLike]] = None,
) -> Dict[str, Fraction]:
    """Calcula las NUEVE distancias; nunca elimina etiquetas coincidentes."""
    center = geometry.center if center is None else geo_as_point(center)
    radius = geometry.radius_squared if radius_squared is None else geo_exact_fraction(radius_squared)
    actual_points = geo_configuration_points(geometry, points)
    return {
        label: 4 * (geo_distance_squared(actual_points[label], center) - radius)
        for label in POINT_LABELS
    }


def objective_error(geometry: NinePointGeometry, candidate_center: PointLike) -> Fraction:
    """J de (4), útil como referencia exacta para la evaluación entera del GA."""
    center = geo_as_point(candidate_center)
    residues = (
        4 * geo_distance_squared(point, center) - geometry.circumradius_squared
        for point in geometry.side_midpoints
    )
    return sum((residue * residue for residue in residues), Fraction(0))


def geo_configuration_points(
    geometry: NinePointGeometry,
    points: Optional[Mapping[str, PointLike]],
) -> Dict[str, Point]:
    if points is None:
        return geometry.points
    if not isinstance(points, Mapping) or set(points) != set(POINT_LABELS):
        raise ValueError("La configuración debe contener exactamente Ma..Mc, Da..Dc y Ea..Ec.")
    return {label: geo_as_point(points[label]) for label in POINT_LABELS}


AUXILIARY_CHECK_DESCRIPTION = (
    "Reconstrucción explícita de 21 controles: tres igualdades de distancia al "
    "circuncentro; tres incidencias del ortocentro en las alturas; para cada uno "
    "de los tres pies, pertenencia a la recta, ortogonalidad de la altura, "
    "s = 2R² - 2b·c, b·v = -s/2 y 2d - h = -a + (2k/s)v. Las identidades "
    "utilizan coordenadas trasladadas al circuncentro. Varias son dependientes; "
    "V8 solo da el total de controles y no permite recuperar su desglose original."
)


def auxiliary_checks(geometry: NinePointGeometry) -> Dict[str, bool]:
    """Las 21 comprobaciones nombradas, sin añadir igualdades vacías de relleno.

    Los cinco controles de cada pie conectan la construcción de (7) con las
    identidades de la demostración. La igualdad de norma final se comprueba aparte
    mediante los nueve residuos; no se cuenta de nuevo para completar este total.
    """
    triangle = geometry.triangle
    origin = geometry.circumcenter
    translated = tuple(vertex - origin for vertex in triangle.vertices)
    h = geometry.orthocenter - origin
    points = geometry.points
    checks: Dict[str, bool] = {}
    for index, suffix in enumerate(("a", "b", "c")):
        vertex = triangle.vertices[index]
        start = triangle.vertices[(index + 1) % 3]
        end = triangle.vertices[(index + 2) % 3]
        aa, bb, cc = translated[index], translated[(index + 1) % 3], translated[(index + 2) % 3]
        foot = points["D" + suffix]
        direction = cc - bb
        s = geo_norm_squared(direction)
        k = geo_dot(aa, direction)
        d = foot - origin
        checks["circumcenter_distance_" + suffix] = geo_distance_squared(vertex, origin) == geometry.circumradius_squared
        checks["orthocenter_altitude_" + suffix] = geo_dot(geometry.orthocenter - vertex, end - start) == 0
        checks["foot_on_line_" + suffix] = geo_cross(foot - start, end - start) == 0
        checks["foot_perpendicular_" + suffix] = geo_dot(vertex - foot, end - start) == 0
        checks["side_norm_identity_" + suffix] = s == 2 * geometry.circumradius_squared - 2 * geo_dot(bb, cc)
        checks["projection_dot_identity_" + suffix] = geo_dot(bb, direction) == -s / 2
        checks["reflection_identity_" + suffix] = 2 * d - h == -aa + direction * (2 * k / s)
    return checks


def verify_configuration(
    geometry: NinePointGeometry,
    center: Optional[PointLike] = None,
    radius_squared: Optional[ExactScalar] = None,
    points: Optional[Mapping[str, PointLike]] = None,
) -> Dict[str, Any]:
    """Verifica tanto las definiciones geométricas como los nueve residuos.

    Un centro candidato del GA se pasa en ``center``. Los controles pueden cambiar
    radio o posiciones. La referencia permanece intacta. Se informan por separado
    la aceptación completa y la de distancias, para mostrar el falso positivo que
    se obtendría al aceptar puntos solo por pertenecer a la circunferencia.
    """
    actual_center = geometry.center if center is None else geo_as_point(center)
    actual_radius = geometry.radius_squared if radius_squared is None else geo_exact_fraction(radius_squared)
    actual_points = geo_configuration_points(geometry, points)
    triangle = geometry.triangle
    base = {
        "non_collinear": triangle.delta != 0,
        "positive_circumradius_squared": geometry.circumradius_squared > 0,
        "positive_candidate_radius_squared": actual_radius > 0,
        "center_is_midpoint_OH": 2 * actual_center == geometry.circumcenter + geometry.orthocenter,
        "radius_is_R_squared_over_four": 4 * actual_radius == geometry.circumradius_squared,
        "reference_auxiliary_checks": all(auxiliary_checks(geometry).values()),
    }
    construction: Dict[str, bool] = {}
    for index, suffix in enumerate(("a", "b", "c")):
        vertex = triangle.vertices[index]
        start = triangle.vertices[(index + 1) % 3]
        end = triangle.vertices[(index + 2) % 3]
        side_midpoint = actual_points["M" + suffix]
        foot = actual_points["D" + suffix]
        euler_point = actual_points["E" + suffix]
        construction["side_midpoint_" + suffix] = 2 * side_midpoint == start + end
        construction["foot_on_line_" + suffix] = geo_cross(foot - start, end - start) == 0
        construction["foot_perpendicular_" + suffix] = geo_dot(vertex - foot, end - start) == 0
        construction["euler_midpoint_" + suffix] = 2 * euler_point == vertex + geometry.orthocenter
    residues = nine_point_residuals(geometry, actual_center, actual_radius, actual_points)
    distance_ok = all(value == 0 for value in residues.values())
    return {
        "accepted": all(base.values()) and all(construction.values()) and distance_ok,
        "distance_only_accepted": distance_ok,
        "base_checks": base,
        "construction_checks": construction,
        "residuals": residues,
        "failures": [name for name, passed in {**base, **construction}.items() if not passed]
        + ["nonzero_residual_" + label for label, value in residues.items() if value != 0],
    }


def algebraic_trace(geometry: NinePointGeometry) -> Dict[str, Any]:
    """Traza racional de (8), (9) y (10), repetida por permutación a, b, c.

    Se guardan los valores de ambos miembros y de los dos términos que se
    cancelan. Así puede verse que se cancelan -4k²/s y +4k²/s, no k con s.
    """
    origin = geometry.circumcenter
    vectors = tuple(vertex - origin for vertex in geometry.triangle.vertices)
    h = geometry.orthocenter - origin
    n = geometry.center - origin
    points = geometry.points
    rows: List[Dict[str, Any]] = []
    for index, suffix in enumerate(("a", "b", "c")):
        aa, bb, cc = vectors[index], vectors[(index + 1) % 3], vectors[(index + 2) % 3]
        m = points["M" + suffix] - origin
        t = points["E" + suffix] - origin
        d = points["D" + suffix] - origin
        v = cc - bb
        s, k = geo_norm_squared(v), geo_dot(aa, v)
        projection_expression = bb + v * (k / s + Fraction(1, 2))
        w = 2 * d - h
        w_expression = -aa + v * (2 * k / s)
        cross_term = -(4 * k / s) * geo_dot(aa, v)
        final_term = (4 * k * k / (s * s)) * geo_norm_squared(v)
        expanded_norm = geo_norm_squared(aa) + cross_term + final_term
        checks = {
            "equal_vertex_radius": geo_norm_squared(aa) == geometry.circumradius_squared,
            "equation_8_side_midpoint": m - n == -aa / 2,
            "equation_8_euler_midpoint": t - n == aa / 2,
            "positive_projection_denominator": s > 0,
            "side_norm_identity": s == 2 * geometry.circumradius_squared - 2 * geo_dot(bb, cc),
            "projection_dot_identity": geo_dot(bb, v) == -s / 2,
            "translated_projection": d == projection_expression,
            "equation_9_vector_identity": w == w_expression,
            "equation_10_expansion": geo_norm_squared(w) == expanded_norm,
            "equation_10_cancellation": cross_term + final_term == 0,
            "equation_10_radius": expanded_norm == geometry.circumradius_squared,
            "foot_center_difference": d - n == w / 2,
            "foot_radius_squared": geo_norm_squared(d - n) == geometry.radius_squared,
        }
        rows.append({
            "vertex": suffix,
            "a_vector": aa, "b_vector": bb, "c_vector": cc,
            "v": v, "s": s, "k": k,
            "equation_8": {
                "m_minus_n": m - n, "minus_a_over_two": -aa / 2,
                "t_minus_n": t - n, "a_over_two": aa / 2,
            },
            "equation_9": {
                "d": d, "projection_expression": projection_expression,
                "w": w, "minus_a_plus_2k_v_over_s": w_expression,
            },
            "equation_10": {
                "a_norm_squared": geo_norm_squared(aa),
                "cross_term": cross_term, "final_term": final_term,
                "cross_plus_final": cross_term + final_term,
                "expanded_norm_squared": expanded_norm,
                "direct_norm_squared": geo_norm_squared(w),
                "expected_R_squared": geometry.circumradius_squared,
                "d_minus_n": d - n, "w_over_two": w / 2,
                "distance_squared": geo_norm_squared(d - n),
                "expected_r_squared": geometry.radius_squared,
            },
            "checks": checks,
            "all_checks_passed": all(checks.values()),
        })
    common_checks = {"h_equals_a_plus_b_plus_c": h == vectors[0] + vectors[1] + vectors[2], "n_equals_h_over_two": n == h / 2}
    return {
        "origin_O": origin, "h": h, "n": n,
        "R_squared": geometry.circumradius_squared,
        "common_checks": common_checks,
        "vertices": rows,
        "all_checks_passed": all(common_checks.values()) and all(row["all_checks_passed"] for row in rows),
    }


def altered_controls(geometry: NinePointGeometry) -> Dict[str, Dict[str, Any]]:
    """Las cuatro alteraciones de la tabla 3, sin cambiar los otros seis puntos."""
    base_points = geometry.points
    feet = dict(base_points)
    euler = dict(base_points)
    vertices = geometry.triangle.vertices
    for index, suffix in enumerate(("a", "b", "c")):
        vertex, start, end = vertices[index], vertices[(index + 1) % 3], vertices[(index + 2) % 3]
        feet["D" + suffix] = start + (end - start) / 3
        euler["E" + suffix] = (2 * vertex + geometry.orthocenter) / 3
    return {
        "shifted_center": {
            "center": geometry.center + Point(1, 0),
            "radius_squared": geometry.radius_squared,
            "points": dict(base_points), "counted_labels": POINT_LABELS,
        },
        "wrong_radius": {
            "center": geometry.center,
            "radius_squared": geometry.circumradius_squared / 3,
            "points": dict(base_points), "counted_labels": POINT_LABELS,
        },
        "third_feet": {
            "center": geometry.center, "radius_squared": geometry.radius_squared,
            "points": feet, "counted_labels": ("Da", "Db", "Dc"),
        },
        "third_euler": {
            "center": geometry.center, "radius_squared": geometry.radius_squared,
            "points": euler, "counted_labels": ("Ea", "Eb", "Ec"),
        },
    }


def example_table_rows() -> List[Dict[str, Any]]:
    """Tabla 1 calculada; las filas son directamente utilizables por csv.DictWriter."""
    geometry = example_geometry()
    residues = nine_point_residuals(geometry)
    families = {"M": "Punto medio de lado", "D": "Pie de altura", "E": "Punto medio de Euler"}
    return [{
        "group": families[label[0]], "point": label,
        "x": point.x, "y": point.y,
        "distance_squared": geo_distance_squared(point, geometry.center),
        "residual": residues[label],
    } for label, point in geometry.named_points]


def euler_distance_counterexample() -> Dict[str, Any]:
    """Ejemplo de 3.3: Ec* pasa la prueba de distancia pero no su construcción.

    Para aislar el motivo, se sustituye SOLO Ec. Las otras ocho posiciones se
    conservan, de modo que el verificador de distancias acepta la configuración
    y el verificador completo la rechaza. Se devuelve también el control que
    sustituye los tres puntos de Euler, que es el empleado en el banco.
    """
    geometry = construct_geometry((-2, -2), (-2, -1), (-1, 0))
    original = geometry.points["Ec"]
    altered = (2 * geometry.triangle.c + geometry.orthocenter) / 3
    points = geometry.points
    points["Ec"] = altered
    check = verify_configuration(geometry, points=points)
    entire_control = altered_controls(geometry)["third_euler"]
    entire_check = verify_configuration(
        geometry, center=entire_control["center"],
        radius_squared=entire_control["radius_squared"], points=entire_control["points"],
    )
    return {
        "triangle": geometry.triangle, "center_N": geometry.center,
        "radius_squared": geometry.radius_squared, "orthocenter_H": geometry.orthocenter,
        "correct_Ec": original, "altered_Ec": altered,
        "correct_offset": original - geometry.center, "altered_offset": altered - geometry.center,
        "correct_distance_squared": geo_distance_squared(original, geometry.center),
        "altered_distance_squared": geo_distance_squared(altered, geometry.center),
        "correct_definition_2Ec": 2 * original == geometry.triangle.c + geometry.orthocenter,
        "altered_definition_2Ec": 2 * altered == geometry.triangle.c + geometry.orthocenter,
        "single_substitution_verification": check,
        "whole_family_verification": entire_check,
    }


def run_geometric_bank(include_details: bool = False) -> Dict[str, Any]:
    """Enumera las 2,300 combinaciones de la rejilla y calcula tablas 4 y 5.

    Los contadores nacen de cero y se actualizan por cada configuración. No se
    presuponen 2,148 triángulos válidos ni los valores de las tablas. La rejilla
    contiene 25 pares ordenados lexicográficamente y combinations evita contar
    permutaciones. No se utiliza ningún generador aleatorio.
    """
    if not isinstance(include_details, bool):
        raise TypeError("include_details debe ser booleano.")
    grid = tuple(Point(x, y) for x in range(-2, 3) for y in range(-2, 3))
    class_counts = {
        name: {"triangles": 0, "residuals_calculated": 0, "zero_residuals": 0}
        for name in TRIANGLE_CLASSES
    }
    controls = {}
    for key in CONTROL_LABELS:
        controls[key] = {
            "configurations": 0, "rejected_configurations": 0,
            "rejected_by_distances": 0, "construction_failed_configurations": 0,
            "all_nine_residues_calculated": 0,
            "positions_examined": 0, "nonzero_residuals": 0, "zero_residuals": 0,
            "untouched_positions_examined": 0, "untouched_zero_residuals": 0,
            "zero_coincidences_unchanged": 0, "zero_coincidences_changed": 0,
            "zero_coincidences_by_class": {name: 0 for name in TRIANGLE_CLASSES},
            "unchanged_zero_coincidences_by_class": {name: 0 for name in TRIANGLE_CLASSES},
        }
    triple_count = collinear = valid = residues_total = zero_total = accepted = 0
    projection_total = projection_positive = auxiliary_total = auxiliary_passed = 0
    auxiliary_failures: List[Dict[str, Any]] = []
    details: List[Dict[str, Any]] = []
    for vertices in combinations(grid, 3):
        triple_count += 1
        if geo_signed_double_area(*vertices) == 0:
            collinear += 1
            continue
        geometry = construct_geometry(*vertices)
        valid += 1
        classification = geometry.triangle.triangle_class
        correct_check = verify_configuration(geometry)
        accepted += int(correct_check["accepted"])
        residues = correct_check["residuals"]
        residues_total += len(residues)
        zero_count = sum(value == 0 for value in residues.values())
        zero_total += zero_count
        class_counts[classification]["triangles"] += 1
        class_counts[classification]["residuals_calculated"] += len(residues)
        class_counts[classification]["zero_residuals"] += zero_count
        projection_total += len(geometry.projection_denominators)
        projection_positive += sum(value > 0 for value in geometry.projection_denominators)
        auxiliary = auxiliary_checks(geometry)
        auxiliary_total += len(auxiliary)
        auxiliary_passed += sum(auxiliary.values())
        failed_auxiliary = [name for name, passed in auxiliary.items() if not passed]
        if failed_auxiliary:
            auxiliary_failures.append({"vertices": vertices, "failures": failed_auxiliary})
        local_controls: Dict[str, Any] = {}
        original_points = geometry.points
        for key, configuration in altered_controls(geometry).items():
            checked = verify_configuration(
                geometry, center=configuration["center"],
                radius_squared=configuration["radius_squared"], points=configuration["points"],
            )
            all_residues = checked["residuals"]
            counted_labels = configuration["counted_labels"]
            stats = controls[key]
            stats["configurations"] += 1
            stats["rejected_configurations"] += int(not checked["accepted"])
            stats["rejected_by_distances"] += int(not checked["distance_only_accepted"])
            stats["construction_failed_configurations"] += int(not all(checked["construction_checks"].values()))
            stats["all_nine_residues_calculated"] += len(all_residues)
            for label, residue in all_residues.items():
                if label not in counted_labels:
                    stats["untouched_positions_examined"] += 1
                    stats["untouched_zero_residuals"] += int(residue == 0)
                    continue
                stats["positions_examined"] += 1
                stats["nonzero_residuals"] += int(residue != 0)
                stats["zero_residuals"] += int(residue == 0)
                if residue == 0:
                    stats["zero_coincidences_by_class"][classification] += 1
                    if key in ("third_feet", "third_euler"):
                        unchanged = configuration["points"][label] == original_points[label]
                        stats["zero_coincidences_unchanged"] += int(unchanged)
                        stats["zero_coincidences_changed"] += int(not unchanged)
                        if unchanged:
                            stats["unchanged_zero_coincidences_by_class"][classification] += 1
            if include_details:
                local_controls[key] = checked
        if include_details:
            details.append({
                "vertices": vertices, "triangle_class": classification,
                "verification": correct_check, "controls": local_controls,
            })
    table4 = [{"class": CLASS_LABELS[key], **class_counts[key]} for key in TRIANGLE_CLASSES]
    table4.append({"class": "Total válido", "triangles": valid, "residuals_calculated": residues_total, "zero_residuals": zero_total})
    table5 = [{
        "control": CONTROL_LABELS[key],
        "rejected_configurations": stats["rejected_configurations"],
        "configurations": stats["configurations"],
        "nonzero_residuals": stats["nonzero_residuals"],
        "positions_examined": stats["positions_examined"],
        "zero_residuals": stats["zero_residuals"],
    } for key, stats in controls.items()]
    report = {
        "grid_points": grid, "grid_point_count": len(grid),
        "total_triples": triple_count, "collinear_triples": collinear,
        "valid_triangles": valid, "accepted_reference_configurations": accepted,
        "residuals_calculated": residues_total, "zero_residuals": zero_total,
        "class_counts": class_counts, "table4_rows": table4,
        "controls": controls, "table5_rows": table5,
        "projection_denominators_calculated": projection_total,
        "positive_projection_denominators": projection_positive,
        "auxiliary_checks_calculated": auxiliary_total,
        "auxiliary_checks_passed": auxiliary_passed,
        "auxiliary_description": AUXILIARY_CHECK_DESCRIPTION,
        "auxiliary_check_names": tuple(auxiliary_checks(example_geometry())),
        "auxiliary_failures": auxiliary_failures,
    }
    if include_details:
        report["details"] = details
    report["published_comparison"] = published_count_comparison(report)
    return report


def published_count_comparison(report: Mapping[str, Any]) -> List[Dict[str, Any]]:
    """Contraste descriptivo con V8; nunca cambia un resultado para hacerlo coincidir."""
    rows: List[Dict[str, Any]] = []

    def compare(name: str, observed: int, published: int) -> None:
        rows.append({"metric": name, "observed": observed, "published": published, "matches": observed == published})

    for key, published in {
        "grid_point_count": 25, "total_triples": 2300, "collinear_triples": 152,
        "valid_triangles": 2148, "residuals_calculated": 19332,
        "zero_residuals": 19332, "positive_projection_denominators": 6444,
        "auxiliary_checks_passed": 45108,
    }.items():
        compare(key, report[key], published)
    for key, published in {"acutangulo": 404, "rectangulo": 596, "obtusangulo": 1148}.items():
        compare(key + "_triangles", report["class_counts"][key]["triangles"], published)
    for key, published in {"shifted_center": 18098, "wrong_radius": 19332, "third_feet": 6340, "third_euler": 5648}.items():
        stats = report["controls"][key]
        compare(key + "_rejected", stats["rejected_configurations"], 2148)
        compare(key + "_nonzero", stats["nonzero_residuals"], published)
        compare(key + "_positions", stats["positions_examined"], 6444 if key in ("third_feet", "third_euler") else 19332)
    for key, field, published in (
        ("third_feet", "zero_coincidences_unchanged", 104),
        ("third_feet", "zero_coincidences_changed", 0),
        ("third_euler", "zero_coincidences_unchanged", 596),
        ("third_euler", "zero_coincidences_changed", 200),
    ):
        compare(key + "_" + field, report["controls"][key][field], published)
    return rows


def geometry_jsonable(value: Any) -> Any:
    """Representación JSON exacta: Fraction se escribe como cadena racional.

    Para CSV pueden utilizarse directamente las filas de tablas: DictWriter
    convierte Fraction a su forma exacta p/q. Esta función evita convertirlo a
    decimal binario al producir JSON o un informe reproducible.
    """
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, Point):
        return {"x": str(value.x), "y": str(value.y)}
    if is_dataclass(value):
        return geometry_jsonable(asdict(value))
    if isinstance(value, Mapping):
        return {str(key): geometry_jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [geometry_jsonable(item) for item in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    raise TypeError("No se conoce una representación JSON para " + type(value).__name__)


def run_geometry_self_checks(include_bank: bool = False) -> Dict[str, Any]:
    """Comprobaciones independientes de ejemplos, rechazos y transformaciones.

    Se usa AssertionError explícito para que la comprobación permanezca activa
    incluso cuando Python se ejecuta con -O. include_bank permite añadir el
    contraste exhaustivo; normalmente el programa principal ya calcula el banco.
    """
    results: List[Dict[str, Any]] = []

    def require(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError("Falló la comprobación geométrica: " + name)
        results.append({"check": name, "passed": True})

    geometry = example_geometry()
    require("ejemplo: circuncentro (2,1)", geometry.circumcenter == Point(2, 1))
    require("ejemplo: ortocentro (1,1)", geometry.orthocenter == Point(1, 1))
    require("ejemplo: centro (3/2,1)", geometry.center == Point(Fraction(3, 2), 1))
    require("ejemplo: radio² 5/4", geometry.radius_squared == Fraction(5, 4))
    expected_points = {
        "Ma": (Fraction(5, 2), Fraction(3, 2)), "Mb": (Fraction(1, 2), Fraction(3, 2)),
        "Mc": (2, 0), "Da": (2, 2), "Db": (Fraction(2, 5), Fraction(6, 5)),
        "Dc": (1, 0), "Ea": (Fraction(1, 2), Fraction(1, 2)),
        "Eb": (Fraction(5, 2), Fraction(1, 2)), "Ec": (1, 2),
    }
    require("nueve coordenadas de tabla 1", all(geometry.points[key] == geo_as_point(value) for key, value in expected_points.items()))
    require("aceptación exacta del ejemplo", verify_configuration(geometry)["accepted"])
    require("rechazo de centro próximo con error positivo", not verify_configuration(geometry, center=(Fraction(96, 64), Fraction(63, 64)))["accepted"])
    for point, expected in (((Fraction(3, 2), Fraction(1, 2)), 27), ((Fraction(1, 2), 1), 224), ((0, 0), 987), ((3, 3), 2091), ((Fraction(1, 2), Fraction(3, 2)), 315)):
        require("J exacto en " + str(point), objective_error(geometry, point) == expected)
    require("J del centro exacto", objective_error(geometry, geometry.center) == 0)
    for vertices in (((0, 0), (1, 1), (2, 2)), ((0, 0), (0, 0), (1, 1))):
        try:
            construct_geometry(*vertices)
        except ValueError:
            rejected = True
        else:
            rejected = False
        require("rechazo de entrada degenerada " + str(vertices), rejected)
    try:
        Point(0.1, 0)
    except TypeError:
        rejected_float = True
    else:
        rejected_float = False
    require("rechazo de coordenada flotante implícita", rejected_float)
    right_triangle = construct_geometry((0, 0), (2, 0), (0, 2))
    obtuse_triangle = construct_geometry((0, 0), (3, 0), (1, 1))
    require("clasificación acutángula", geometry.triangle.triangle_class == "acutangulo")
    require("clasificación rectángula", right_triangle.triangle.triangle_class == "rectangulo")
    require("clasificación obtusángula", obtuse_triangle.triangle.triangle_class == "obtusangulo")
    require("rectángulo conserva nueve etiquetas coincidentes", len(right_triangle.named_points) == 9 and len(set(right_triangle.points.values())) < 9 and verify_configuration(right_triangle)["accepted"])
    require("proyección exterior admitida", geo_project_onto_line((0, 0), (3, 0), (1, 1)) == Point(Fraction(3, 5), Fraction(6, 5)))
    require("triángulo obtuso aceptado", verify_configuration(obtuse_triangle)["accepted"])
    # La covariancia por traslado y escala contrasta las fórmulas sin reutilizar
    # coordenadas esperadas construidas por el mismo procedimiento.
    shift, scale = Point(Fraction(7, 3), Fraction(-5, 2)), Fraction(-3, 2)
    transformed = construct_geometry(*(vertex * scale + shift for vertex in geometry.triangle.vertices))
    require("centro covariante por escala y traslado", transformed.center == geometry.center * scale + shift)
    require("radio² escala con el cuadrado", transformed.radius_squared == geometry.radius_squared * scale * scale)
    require("nueve construcciones covariantes", all(transformed.points[label] == point * scale + shift for label, point in geometry.named_points))
    require("21 auxiliares explícitas satisfechas", len(auxiliary_checks(geometry)) == 21 and all(auxiliary_checks(geometry).values()))
    traces = [algebraic_trace(item) for item in (geometry, right_triangle, obtuse_triangle)]
    require("trazas (8)-(10) en las tres clases", all(trace["all_checks_passed"] for trace in traces))
    counterexample = euler_distance_counterexample()
    require("contraejemplo: N y r² publicados", counterexample["center_N"] == Point(Fraction(-9, 4), Fraction(-3, 4)) and counterexample["radius_squared"] == Fraction(5, 8))
    require("contraejemplo: Ec y Ec* publicados", counterexample["correct_Ec"] == Point(Fraction(-5, 2), 0) and counterexample["altered_Ec"] == Point(-2, 0))
    require("Ec* pasa distancias pero falla construcción", counterexample["single_substitution_verification"]["distance_only_accepted"] and not counterexample["single_substitution_verification"]["accepted"] and not counterexample["altered_definition_2Ec"])
    report: Dict[str, Any] = {"passed": True, "checks": results, "example_trace": traces[0], "euler_counterexample": counterexample}
    if include_bank:
        bank = run_geometric_bank()
        require("banco: todos los originales aceptados", bank["accepted_reference_configurations"] == bank["valid_triangles"])
        require("banco: coincidencia con los conteos publicados", all(row["matches"] for row in bank["published_comparison"]))
        require("banco: seis posiciones no alteradas se verifican", all(bank["controls"][key]["untouched_positions_examined"] == bank["controls"][key]["untouched_zero_residuals"] == 6 * bank["valid_triangles"] for key in ("third_feet", "third_euler")))
        require("banco: 596 coincidencias Euler intactas en rectángulos", bank["controls"]["third_euler"]["unchanged_zero_coincidences_by_class"]["rectangulo"] == 596)
        report["bank"] = bank
    return report

"""Componente genético autocontenido para ARTICULO-01-NUEVE-PUNTOS-V8.

Al integrar este bloque en el programa final no se requieren archivos propios.
La biblioteca estándar basta para la representación binaria, la aritmética
exacta, el generador y el registro. No se ejecuta ningún experimento al importar.

Las siete etapas se completan por bloques: 98 torneos, 49 cruces y después la
mutación de los 98 hijos con los parámetros publicados. Esta elección fija una
traza reproducible, pero el artículo no documenta todos los detalles necesarios
para identificarla con la traza original. Nunca se modifica una semilla para
obtener una cantidad de éxitos determinada.
"""

from dataclasses import dataclass as ga_dataclass, field as ga_field
from fractions import Fraction
import math as ga_math
import numbers as ga_numbers
import random as ga_random
from collections.abc import Mapping as ga_Mapping, Sequence as ga_Sequence
from typing import Callable as ga_Callable, Any as ga_Any


def ga_require_integer(value: int, name: str, minimum: int | None = None,
                       maximum: int | None = None) -> int:
    """Valida un entero sin aceptar True/False como si fueran cantidades."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} debe ser un entero.")
    if minimum is not None and value < minimum:
        raise ValueError(f"{name} debe ser al menos {minimum}.")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} no puede superar {maximum}.")
    return value


def ga_require_probability(value: float, name: str) -> float:
    """Normaliza una probabilidad finita al tipo usado por random()."""
    if isinstance(value, bool) or not isinstance(value, ga_numbers.Real):
        raise TypeError(f"{name} debe ser un número real entre 0 y 1.")
    result = float(value)
    if not ga_math.isfinite(result) or not 0.0 <= result <= 1.0:
        raise ValueError(f"{name} debe ser finita y pertenecer a [0, 1].")
    return result


def ga_as_fraction(value: ga_Any, name: str) -> Fraction:
    """Convierte un dato exacto a Fraction sin introducir un redondeo oculto.

    Se admiten enteros, Fraction y cadenas que Fraction pueda interpretar.
    Se rechazan floats: los datos geométricos deben conservar su significado
    racional antes de entrar al GA, especialmente al verificar una solución.
    """
    if isinstance(value, bool) or not isinstance(value, (int, Fraction, str)):
        raise TypeError(f"{name} debe ser int, Fraction o una cadena racional.")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f"{name} no representa una fracción válida.") from error


@ga_dataclass(frozen=True, slots=True)
class GAConfig:
    """Parámetros del algoritmo; los valores por defecto son los de V8.

    Otros valores permiten pruebas pequeñas o experimentos declarados. No
    deben confundirse sus resultados con los del protocolo publicado. Como
    cada pareja produce dos hijos, population_size - elitism debe ser par.
    Se admite elitism=0 para una exploración explícita; en ese caso no existe
    la garantía de conservación del mejor error. También se admite conservar
    toda la población, aunque tal configuración no genera descendencia.
    """

    population_size: int = 100
    generations: int = 500
    crossover_probability: float = 0.90
    mutation_probability: float = 0.01
    elitism: int = 2

    def __post_init__(self) -> None:
        ga_require_integer(self.population_size, "population_size", minimum=2)
        ga_require_integer(self.generations, "generations", minimum=0)
        ga_require_integer(self.elitism, "elitism", minimum=0,
                           maximum=self.population_size)
        if (self.population_size - self.elitism) % 2:
            raise ValueError("La cantidad de hijos debe ser par: population_size - elitism.")
        object.__setattr__(self, "crossover_probability",
                           ga_require_probability(self.crossover_probability,
                                                  "crossover_probability"))
        object.__setattr__(self, "mutation_probability",
                           ga_require_probability(self.mutation_probability,
                                                  "mutation_probability"))

    @property
    def offspring_count(self) -> int:
        """Número de posiciones ocupadas por hijos en cada generación."""
        return self.population_size - self.elitism


def ga_validate_code(code: int) -> int:
    """Un cromosoma es un entero inmutable de exactamente 16 posiciones."""
    return ga_require_integer(code, "cromosoma", minimum=0, maximum=65535)


def ga_encode_chromosome(u: int, v: int) -> int:
    """Concatena los ocho bits de u y los ocho de v, sin perder ceros."""
    ga_require_integer(u, "u", minimum=0, maximum=255)
    ga_require_integer(v, "v", minimum=0, maximum=255)
    return (u << 8) | v


def ga_decode_chromosome(code: int) -> tuple[Fraction, Fraction]:
    """Devuelve Q=(u/64,v/64); nunca aproxima las coordenadas con float."""
    ga_validate_code(code)
    return Fraction(code >> 8, 64), Fraction(code & 255, 64)


def ga_format_chromosome(code: int) -> str:
    """Forma legible que conserva las 16 posiciones y separa coordenadas."""
    ga_validate_code(code)
    return f"{code >> 8:08b}|{code & 255:08b}"


@ga_dataclass(frozen=True, slots=True)
class GAFitnessModel:
    """Modelo entero de J construido a partir de tres puntos medios y R².

    El modelo no recibe, deduce ni utiliza N para orientar la búsqueda. Usa
    exclusivamente la definición J = sum((4*distancia² - R²)²). Al expresar
    las coordenadas con escala 64, cada residuo tiene denominador 64²/4=1024;
    por ello J tiene denominador 1024²=1048576. Estos valores se derivan aquí
    de la codificación, en lugar de ajustar coeficientes al óptimo conocido.

    Se exige compatibilidad de los datos con esos denominadores. Esta clase
    representa la codificación concreta de V8, no cualquier rejilla racional.
    """

    midpoints: tuple[tuple[Fraction, Fraction], ...]
    R2: Fraction
    coordinate_scale: int = ga_field(default=64, init=False)
    scaled_midpoints: tuple[tuple[int, int], ...] = ga_field(init=False)
    residual_denominator: int = ga_field(init=False)
    fitness_denominator: int = ga_field(init=False)
    radius_numerator: int = ga_field(init=False)

    def __post_init__(self) -> None:
        if len(self.midpoints) != 3:
            raise ValueError("La evaluación requiere exactamente tres puntos medios.")
        normalized = []
        for index, point in enumerate(self.midpoints):
            if not isinstance(point, ga_Sequence) or isinstance(point, (str, bytes)) or len(point) != 2:
                raise ValueError(f"El punto medio {index} debe contener dos coordenadas.")
            normalized.append((ga_as_fraction(point[0], f"punto {index}, x"),
                               ga_as_fraction(point[1], f"punto {index}, y")))
        points = tuple(normalized)
        radius_squared = ga_as_fraction(self.R2, "R2")
        if radius_squared <= 0:
            raise ValueError("R2 debe ser estrictamente positivo.")
        a, b, c = points
        determinant = ((b[0] - a[0]) * (c[1] - a[1])
                       - (b[1] - a[1]) * (c[0] - a[0]))
        if determinant == 0:
            raise ValueError("Los tres puntos medios deben ser no colineales.")

        scaled = []
        for point in points:
            values = tuple(coordinate * self.coordinate_scale for coordinate in point)
            if any(value.denominator != 1 for value in values):
                raise ValueError("Los puntos medios deben ser compatibles con la escala 64.")
            scaled.append((values[0].numerator, values[1].numerator))
        residual_denominator = self.coordinate_scale ** 2 // 4
        radius_numerator = radius_squared * residual_denominator
        if radius_numerator.denominator != 1:
            raise ValueError("R2 debe ser compatible con el denominador residual 1024.")
        object.__setattr__(self, "midpoints", points)
        object.__setattr__(self, "R2", radius_squared)
        object.__setattr__(self, "scaled_midpoints", tuple(scaled))
        object.__setattr__(self, "residual_denominator", residual_denominator)
        object.__setattr__(self, "fitness_denominator", residual_denominator ** 2)
        object.__setattr__(self, "radius_numerator", radius_numerator.numerator)

    @classmethod
    def from_geometry_data(cls, midpoints: ga_Any, R2: ga_Any) -> "GAFitnessModel":
        """Acepta tres pares o un diccionario con las claves Ma, Mb y Mc.

        La geometría puede suministrar [p.as_pair() for p in side_midpoints].
        No se acepta ni se requiere el centro exacto como argumento.
        """
        if isinstance(midpoints, ga_Mapping):
            try:
                ordered = tuple(midpoints[label] for label in ("Ma", "Mb", "Mc"))
            except KeyError as error:
                raise ValueError("El diccionario debe contener Ma, Mb y Mc.") from error
        else:
            try:
                ordered = tuple(midpoints)
            except TypeError as error:
                raise TypeError("midpoints debe contener tres pares de coordenadas.") from error
        return cls(ordered, ga_as_fraction(R2, "R2"))

    def decode(self, code: int) -> tuple[Fraction, Fraction]:
        """Recupera el centro candidato representado por un cromosoma."""
        return ga_decode_chromosome(code)

    def residual_numerators(self, code: int) -> tuple[int, int, int]:
        """Devuelve los tres n_i tales que e_i=n_i/1024, en orden Ma,Mb,Mc."""
        ga_validate_code(code)
        u, v = code >> 8, code & 255
        result = tuple((u - x) ** 2 + (v - y) ** 2 - self.radius_numerator
                       for x, y in self.scaled_midpoints)
        return result

    def evaluate(self, code: int) -> int:
        """Calcula K=sum(n_i²), suficiente para comparar errores exactamente."""
        return sum(value * value for value in self.residual_numerators(code))

    def k_to_j(self, K: int) -> Fraction:
        """Convierte un numerador ya evaluado sin volver a evaluar el genoma."""
        ga_require_integer(K, "K", minimum=0)
        return Fraction(K, self.fitness_denominator)

    def j_value(self, code: int) -> Fraction:
        """Devuelve J exacto; la ejecución compara K para evitar trabajo extra."""
        return self.k_to_j(self.evaluate(code))


def ga_validate_population(population: ga_Sequence[int], expected_size: int | None = None) -> None:
    """Rechaza poblaciones o códigos incompatibles antes de un operador."""
    if expected_size is not None and len(population) != expected_size:
        raise ValueError(f"Se esperaban {expected_size} cromosomas, no {len(population)}.")
    for code in population:
        ga_validate_code(code)


def ga_validate_fitness_inputs(population: ga_Sequence[int], fitness: ga_Sequence[int],
                               expected_size: int) -> None:
    """Comprueba la correspondencia entre posiciones y errores evaluados."""
    ga_validate_population(population, expected_size)
    if len(fitness) != expected_size:
        raise ValueError("Debe existir un error entero por cada cromosoma.")
    for value in fitness:
        ga_require_integer(value, "error K", minimum=0)


def etapa_1_inicializar(rng: ga_random.Random, config: GAConfig) -> list[int]:
    """Etapa 1: construye P(0) con bits equiprobables e independientes.

    Cada nuevo bit se añade a la derecha después de desplazar el prefijo.
    Así, la primera llamada produce el bit más significativo. Con los valores
    de V8 se hacen exactamente 100*16=1600 llamadas a getrandbits(1). No se
    sustituyen por getrandbits(16): esa llamada tendría otra traza aleatoria.
    Tampoco se descartan duplicados ni se introduce una solución conocida.
    """
    population = []
    for _ in range(config.population_size):
        code = 0
        for _ in range(16):
            code = (code << 1) | rng.getrandbits(1)
        population.append(code)
    return population


def etapa_2_evaluar(population: ga_Sequence[int], model: GAFitnessModel) -> list[int]:
    """Etapa 2: evalúa toda la población, incluidas las copias de la élite.

    La lista de K conserva exactamente el orden de los cromosomas. Aunque
    podrían reutilizarse errores de individuos repetidos, aquí se evalúan las
    100 posiciones de cada población para respetar el presupuesto publicado.
    Este procedimiento no consume números aleatorios ni redondea resultados.
    """
    return [model.evaluate(code) for code in population]


def etapa_3_seleccionar(population: ga_Sequence[int], fitness: ga_Sequence[int],
                        rng: ga_random.Random, config: GAConfig,
                        trace: dict | None = None) -> list[int]:
    """Etapa 3: realiza todos los torneos antes del primer cruce.

    Dentro de cada torneo se sortean dos índices distintos. Entre torneos sí
    puede repetirse un índice: un individuo puede aportar varios progenitores.
    Un empate siempre consume choice, incluso si ambos genomas son iguales.
    Evitar ese sorteo cambiaría los sorteos siguientes de la misma corrida.
    Se selecciona sobre P(g) en su orden previo; no sobre una lista ordenada.
    """
    ga_validate_fitness_inputs(population, fitness, config.population_size)
    parents = []
    records = [] if trace is not None else None
    for tournament_index in range(config.offspring_count):
        i, j = rng.sample(range(config.population_size), 2)
        tied = fitness[i] == fitness[j]
        if fitness[i] < fitness[j]:
            winner = i
        elif fitness[j] < fitness[i]:
            winner = j
        else:
            winner = rng.choice((i, j))
        parents.append(population[winner])
        if records is not None:
            records.append({"tournament_index": tournament_index,
                            "indices": [i, j],
                            "candidate_codes": [population[i], population[j]],
                            "candidate_k": [fitness[i], fitness[j]],
                            "tied": tied, "winner_index": winner,
                            "winner_code": population[winner]})
    if trace is not None:
        trace["tournaments"] = records
    return parents


def ga_crossover_at(first: int, second: int, cut: int) -> tuple[int, int]:
    """Cruza dos códigos después de cut bits contados desde la izquierda.

    La máscara contiene unos únicamente en el sufijo que se intercambia.
    El primer hijo conserva el prefijo del primer padre; el segundo, el del
    segundo padre. Un corte después del bit ocho intercambia coordenadas y
    los demás cortes pueden modificar una coordenada dentro de su bloque.
    """
    ga_validate_code(first)
    ga_validate_code(second)
    ga_require_integer(cut, "corte", minimum=1, maximum=15)
    suffix_mask = (1 << (16 - cut)) - 1
    prefix_mask = 65535 ^ suffix_mask
    return ((first & prefix_mask) | (second & suffix_mask),
            (second & prefix_mask) | (first & suffix_mask))


def etapa_4_cruzar(parents: ga_Sequence[int], rng: ga_random.Random, config: GAConfig,
                   trace: dict | None = None) -> tuple[list[int], dict[str, int]]:
    """Etapa 4: produce dos hijos por pareja mediante cruce de un punto.

    Cada pareja consume un random(), se cruce o no. Solo una pareja que sí
    se cruza consume randrange(1,16) para elegir el corte. Los hijos se guardan
    en el orden de parejas y, dentro de cada pareja, primero el hijo 1 y luego
    el hijo 2. Las copias sin cruce también pasan por la etapa de mutación.
    """
    ga_validate_population(parents, config.offspring_count)
    children = []
    crossover_count = 0
    records = [] if trace is not None else None
    for offset in range(0, len(parents), 2):
        first, second = parents[offset], parents[offset + 1]
        draw = rng.random()
        crossed = draw < config.crossover_probability
        cut = rng.randrange(1, 16) if crossed else None
        pair_children = ga_crossover_at(first, second, cut) if crossed else (first, second)
        children.extend(pair_children)
        crossover_count += int(crossed)
        if records is not None:
            records.append({"pair_index": offset // 2,
                            "parent_codes": [first, second], "draw": draw,
                            "crossed": crossed, "cut": cut,
                            "child_codes": list(pair_children)})
    if trace is not None:
        trace["crossovers"] = records
    pair_count = len(parents) // 2
    return children, {"pairs": pair_count, "crossovers": crossover_count,
                      "copied_pairs": pair_count - crossover_count}


def etapa_5_mutar(children: ga_Sequence[int], rng: ga_random.Random, config: GAConfig,
                  trace: dict | None = None) -> tuple[list[int], dict[str, int]]:
    """Etapa 5: decide independientemente la inversión de cada bit.

    Se recorre cada cromosoma de izquierda a derecha: posiciones 1 a 16,
    equivalentes a desplazamientos binarios 15 a 0. Siempre se realizan los
    16 sorteos, incluso con probabilidad 0 o 1. La traza guarda estos mismos
    valores cuando se solicita; registrar la ejecución no añade sorteos.
    La élite no entra en esta función: solo se reciben los hijos nuevos.
    """
    ga_validate_population(children, config.offspring_count)
    mutated = []
    mutated_bits = 0
    mutated_children = 0
    records = [] if trace is not None else None
    for child_index, original in enumerate(children):
        code = original
        draws = [] if records is not None else None
        flipped_positions = []
        for shift in range(15, -1, -1):
            draw = rng.random()
            if draws is not None:
                draws.append(draw)
            if draw < config.mutation_probability:
                code ^= 1 << shift
                flipped_positions.append(16 - shift)
        mutated.append(code)
        mutated_bits += len(flipped_positions)
        mutated_children += int(bool(flipped_positions))
        if records is not None:
            records.append({"child_index": child_index,
                            "before_code": original, "after_code": code,
                            "draws": draws, "flipped_positions": flipped_positions})
    if trace is not None:
        trace["mutations"] = records
    return mutated, {"mutation_trials": len(children) * 16,
                     "mutated_bits": mutated_bits,
                     "mutated_children": mutated_children}


def etapa_6_reemplazar(population: ga_Sequence[int], fitness: ga_Sequence[int],
                       children: ga_Sequence[int], config: GAConfig,
                       trace: dict | None = None) -> list[int]:
    """Etapa 6: antepone copias intactas de la élite a los hijos producidos.

    sorted es estable: dos índices con el mismo K mantienen su orden previo.
    No se usa el cromosoma como segundo criterio. Pueden conservarse dos
    copias del mismo genotipo porque se protegen posiciones de la población.
    El resto de la generación anterior deja de intervenir tras el reemplazo;
    ningún hijo se descarta por ser peor que sus padres.
    """
    ga_validate_fitness_inputs(population, fitness, config.population_size)
    ga_validate_population(children, config.offspring_count)
    elite_indices = sorted(range(len(population)), key=fitness.__getitem__)[:config.elitism]
    elite_codes = [population[index] for index in elite_indices]
    next_population = elite_codes + list(children)
    assert len(next_population) == config.population_size, "Cambió el tamaño poblacional."
    assert next_population[:config.elitism] == elite_codes, "Se alteró una copia de la élite."
    if trace is not None:
        trace["elites"] = [{"previous_index": index, "code": population[index],
                            "k": fitness[index]} for index in elite_indices]
    return next_population


def etapa_7_terminar_y_certificar(population: ga_Sequence[int], fitness: ga_Sequence[int],
                                 generation: int, config: GAConfig, model: GAFitnessModel,
                                 verify_callback: ga_Callable[[tuple[Fraction, Fraction]], dict]
                                 ) -> dict | None:
    """Etapa 7: termina por presupuesto y verifica el mejor candidato final.

    Antes de G devuelve None aunque exista K=0: el éxito temprano se registra,
    pero no interrumpe las 500 transiciones. Al llegar a G se escoge el primer
    mínimo, se recupera Q y se invoca el verificador geométrico independiente.
    Un resultado se acepta solo si su J es cero y el verificador confirma las
    nueve distancias y todas las condiciones geométricas de construcción.
    """
    ga_require_integer(generation, "generation", minimum=0, maximum=config.generations)
    if generation < config.generations:
        return None
    ga_validate_fitness_inputs(population, fitness, config.population_size)
    best_index = min(range(len(population)), key=fitness.__getitem__)
    final_code = population[best_index]
    final_center = model.decode(final_code)
    verification = verify_callback(final_center)
    if not isinstance(verification, dict) or not isinstance(verification.get("accepted"), bool):
        raise TypeError("El verificador debe devolver un dict con accepted de tipo bool.")
    best_k = fitness[best_index]
    return {"final_code": final_code, "final_center": final_center,
            "best_k": best_k, "best_J": model.k_to_j(best_k),
            "accepted": verification["accepted"] and best_k == 0,
            "verification": dict(verification)}


def ga_zero_operator_counts() -> dict[str, int]:
    """P(0) no fue producida por una transición: estos contadores son cero."""
    return {"tournaments": 0, "pairs": 0, "crossovers": 0, "copied_pairs": 0,
            "mutation_trials": 0, "mutated_bits": 0, "mutated_children": 0,
            "elite_copies": 0}


def ga_history_record(generation: int, population: ga_Sequence[int], fitness: ga_Sequence[int],
                      model: GAFitnessModel, operators: dict[str, int]) -> dict:
    """Resume una población evaluada; cada contador describe cómo se produjo.

    Se conserva Fraction en best_J y mean_J. Los gráficos o los formatos de
    salida pueden convertir después a float, sin afectar a selección alguna.
    La diversidad cuenta códigos distintos, no etiquetas ni porcentajes.
    """
    best_k = min(fitness)
    return {"generation": generation, "best_k": best_k,
            "best_J": model.k_to_j(best_k),
            "mean_J": Fraction(sum(fitness), len(population) * model.fitness_denominator),
            "diversity": len(set(population)), "exact_count": fitness.count(0),
            **operators}


def run_ga(seed: int, config: GAConfig, model: GAFitnessModel,
           verify_callback: ga_Callable[[tuple[Fraction, Fraction]], dict],
           population_sink: ga_Callable[[int, int, ga_Sequence[int]], None] | None = None,
           capture_first_transition: bool = False) -> dict:
    """Ejecuta una corrida sin conocer ni insertar el centro buscado.

    El generador es local y se inicializa una sola vez. Su consumo queda
    determinado por las llamadas de las etapas 1, 3, 4 y 5. Los registros, el
    verificador y las conversiones a Fraction no utilizan ese generador.

    population_sink recibe una instantánea inmutable de cada población, desde
    P(0) hasta P(G), para que el programa principal pueda comprimir los genomas
    sin retenerlos todos en memoria. El callback no recibe la población viva.

    Cuando se solicita, se captura la primera transición de esta corrida,
    cualquiera que sea su semilla; el programa principal la pide solo para
    la primera corrida del experimento.
    Contiene P0/K0, los torneos, cruces, mutaciones, élites y P1/K1 reales.
    Si no se solicita o si G=0, first_transition es None.
    """
    ga_require_integer(seed, "seed")
    if not isinstance(config, GAConfig) or not isinstance(model, GAFitnessModel):
        raise TypeError("Se requieren instancias GAConfig y GAFitnessModel.")
    if not callable(verify_callback):
        raise TypeError("verify_callback debe ser invocable.")
    if population_sink is not None and not callable(population_sink):
        raise TypeError("population_sink debe ser invocable o None.")
    if not isinstance(capture_first_transition, bool):
        raise TypeError("capture_first_transition debe ser bool.")

    rng = ga_random.Random(seed)
    population = etapa_1_inicializar(rng, config)
    fitness = etapa_2_evaluar(population, model)
    evaluations = len(population)
    history = [ga_history_record(0, population, fitness, model, ga_zero_operator_counts())]
    first_zero_generation = 0 if min(fitness) == 0 else None
    if population_sink is not None:
        population_sink(seed, 0, tuple(population))

    first_transition = None
    should_capture = capture_first_transition and config.generations > 0
    if should_capture:
        first_transition = {"seed": seed, "from_generation": 0, "to_generation": 1,
                            "P0": list(population), "K0": list(fitness)}

    for generation in range(1, config.generations + 1):
        previous_best = min(fitness)
        trace = first_transition if should_capture and generation == 1 else None
        parents = etapa_3_seleccionar(population, fitness, rng, config, trace)
        children, crossover_counts = etapa_4_cruzar(parents, rng, config, trace)
        children, mutation_counts = etapa_5_mutar(children, rng, config, trace)
        population = etapa_6_reemplazar(population, fitness, children, config, trace)
        fitness = etapa_2_evaluar(population, model)
        evaluations += len(population)
        assert len(population) == config.population_size, "Tamaño poblacional incorrecto."
        if config.elitism:
            assert min(fitness) <= previous_best, "El elitismo perdió el mejor error."
        if first_zero_generation is None and min(fitness) == 0:
            first_zero_generation = generation
        operators = {"tournaments": len(parents), **crossover_counts,
                     **mutation_counts, "elite_copies": config.elitism}
        history.append(ga_history_record(generation, population, fitness, model, operators))
        if trace is not None:
            trace["P1"] = list(population)
            trace["K1"] = list(fitness)
            trace["operator_counts"] = dict(operators)
        if population_sink is not None:
            population_sink(seed, generation, tuple(population))

    # La única comprobación final se ejecuta tras consumir todo el presupuesto.
    # En particular, una corrida exitosa no evalúa menos poblaciones que otra.
    final_result = etapa_7_terminar_y_certificar(population, fitness, config.generations,
                                                config, model, verify_callback)
    assert final_result is not None
    assert evaluations == config.population_size * (config.generations + 1)
    return {"seed": seed, **final_result,
            "first_zero_generation": first_zero_generation,
            "evaluations": evaluations, "history": history,
            "final_population": list(population), "first_transition": first_transition}


def ga_run_self_checks() -> dict:
    """Autocomprobaciones breves y significativas; no repiten 30 corridas.

    Se contrasta la evaluación entera con una expresión racional independiente,
    se reproducen ejemplos verificables y se comprueba que observar la primera
    transición no altera la trayectoria. Solo se usan corridas de dos pasos.
    Un fallo lanza AssertionError; una entrada inválida debe lanzar un error
    explicativo, no corregirse silenciosamente.
    """
    checks = []
    model = GAFitnessModel.from_geometry_data(
        [(Fraction(5, 2), Fraction(3, 2)),
         (Fraction(1, 2), Fraction(3, 2)), (2, 0)], Fraction(5))

    examples = {(96, 32): 27, (32, 64): 224, (0, 0): 987,
                (192, 192): 2091, (32, 32): 251, (32, 96): 315, (96, 64): 0}
    codes = [ga_encode_chromosome(u, v) for u, v in examples]
    for code in codes + [1, 255, 256, 65535]:
        qx, qy = model.decode(code)
        reference = sum((4 * ((px - qx) ** 2 + (py - qy) ** 2) - model.R2) ** 2
                        for px, py in model.midpoints)
        assert model.j_value(code) == reference, "Discrepancia entre enteros y Fraction."
    for (u, v), expected in examples.items():
        assert model.j_value(ga_encode_chromosome(u, v)) == expected
    assert model.residual_denominator == 1024 and model.fitness_denominator == 1048576
    checks.append("Evaluación entera frente a Fraction y siete ejemplos exactos")

    first, second = ga_encode_chromosome(96, 32), ga_encode_chromosome(32, 64)
    crossed = ga_crossover_at(first, second, 8)
    assert crossed == (ga_encode_chromosome(96, 64), ga_encode_chromosome(32, 32))
    assert ga_crossover_at(*crossed, 8) == (first, second)
    checks.append("Cruce después del bit ocho y recuperación de los progenitores")

    rng_zero, rng_one = ga_random.Random(17), ga_random.Random(17)
    zero_config = GAConfig(population_size=4, generations=0, mutation_probability=0, elitism=2)
    one_config = GAConfig(population_size=4, generations=0, mutation_probability=1, elitism=2)
    unchanged, counts_zero = etapa_5_mutar([first, second], rng_zero, zero_config)
    inverted, counts_one = etapa_5_mutar([first, second], rng_one, one_config)
    assert unchanged == [first, second] and counts_zero["mutated_bits"] == 0
    assert inverted == [first ^ 65535, second ^ 65535] and counts_one["mutated_bits"] == 32
    assert counts_zero["mutation_trials"] == counts_one["mutation_trials"] == 32
    assert rng_zero.getstate() == rng_one.getstate(), "La mutación omitió sorteos de un extremo."
    checks.append("Mutación p=0/p=1 y consumo de los 16 sorteos por hijo")

    stable_trace = {}
    replacement = etapa_6_reemplazar([100, 200, 201, 300], [3, 1, 1, 7], [42, 42],
                                      zero_config, stable_trace)
    assert replacement == [200, 201, 42, 42]
    assert [item["previous_index"] for item in stable_trace["elites"]] == [1, 2]
    checks.append("Élite estable en empates y conservación de cromosomas duplicados")

    invalid_configs = [{"population_size": True}, {"population_size": 1},
                       {"generations": -1}, {"generations": 1.5},
                       {"elitism": -1}, {"elitism": 101}, {"elitism": 1},
                       {"crossover_probability": 1.1},
                       {"mutation_probability": float("nan")},
                       {"mutation_probability": True}]
    for arguments in invalid_configs:
        try:
            GAConfig(**arguments)
        except (TypeError, ValueError):
            pass
        else:
            raise AssertionError(f"Se admitió una configuración inválida: {arguments!r}")
    checks.append("Validación de tipos, probabilidades, presupuesto y descendencia par")

    short_config = GAConfig(generations=2)
    sink_records = []
    def ga_test_verifier(center: tuple[Fraction, Fraction]) -> dict:
        # Este callback solo permite probar el contrato; el programa integra
        # su verificador completo de construcciones y nueve distancias.
        return {"accepted": center == (Fraction(3, 2), Fraction(1))}
    def ga_test_sink(seed: int, generation: int, population: ga_Sequence[int]) -> None:
        assert isinstance(population, tuple), "El sink recibió una población mutable."
        sink_records.append((seed, generation, population))
    plain = run_ga(0, short_config, model, ga_test_verifier)
    traced = run_ga(0, short_config, model, ga_test_verifier,
                    population_sink=ga_test_sink, capture_first_transition=True)
    assert plain["final_population"] == traced["final_population"]
    assert plain["history"] == traced["history"]
    assert plain["evaluations"] == traced["evaluations"] == 300
    assert len(sink_records) == 3 and [row[1] for row in sink_records] == [0, 1, 2]
    captured = traced["first_transition"]
    assert len(captured["tournaments"]) == 98
    assert len(captured["crossovers"]) == 49
    assert len(captured["mutations"]) == 98
    assert len(captured["elites"]) == 2
    assert captured["P0"] == list(sink_records[0][2])
    assert captured["P1"] == list(sink_records[1][2])
    assert all(len(record["draws"]) == 16 for record in captured["mutations"])
    assert all(traced["history"][0][name] == 0 for name in ga_zero_operator_counts())
    assert all(isinstance(row["best_J"], Fraction) and isinstance(row["mean_J"], Fraction)
               for row in traced["history"])
    assert etapa_7_terminar_y_certificar(sink_records[0][2], captured["K0"], 0,
                                        short_config, model, ga_test_verifier) is None
    checks.append("Captura y sink sin efecto sobre la trayectoria ni el presupuesto")
    return {"passed": True, "count": len(checks), "checks": checks}

"""Figuras del experimento de la circunferencia de los nueve puntos.

La única dependencia externa de este componente es Matplotlib. No se importa
NumPy directamente, no se instalan paquetes y no se leen archivos del proyecto.
Las figuras de resultados reciben todos sus datos del programa que las llama.
El ejemplo manual se calcula aparte y se identifica como ilustrativo.

Convención de la rejilla: ``fitness_grid[v][u]`` contiene J(u/64, v/64).
Cada figura se guarda en PNG de 300 dpi y en SVG vectorial. El paisaje contiene
una imagen de los valores de la rejilla dentro del SVG; sus rótulos, marcadores
y ejes siguen siendo vectoriales.
"""


from collections import Counter, defaultdict
from fractions import Fraction
import math
from pathlib import Path
from statistics import median
from typing import Any


_PLOT_PURPLE = "#7135A7"
_PLOT_BLUE = "#2A5C9D"
_PLOT_TEAL = "#008791"
_PLOT_ORANGE = "#C45A20"
_PLOT_GOLD = "#E8B63B"
_PLOT_INK = "#24222B"
_PLOT_GRAY = "#716B79"
_PLOT_LIGHT = "#F4F0F8"


def _plot_float(value: Any, name: str) -> float:
    """Convierte únicamente para dibujar; nunca decide aceptación o igualdad."""
    try:
        result = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"{name} debe ser un número representable.") from exc
    if not math.isfinite(result):
        raise ValueError(f"{name} debe ser finito.")
    return result


def _plot_point(value: Any, name: str) -> tuple[float, float]:
    if not isinstance(value, (tuple, list)) or len(value) != 2:
        raise ValueError(f"{name} debe contener exactamente dos coordenadas.")
    return _plot_float(value[0], name + ".x"), _plot_float(value[1], name + ".y")


def _plot_fraction_label(value: Any) -> str:
    """Rótulo breve para las coordenadas racionales de este experimento.

    Las coordenadas gráficas llegan como float, pero las del ejemplo y las de la
    rejilla tienen denominadores pequeños. Esta aproximación se limita al rótulo;
    no interviene en la geometría, la aptitud ni la certificación.
    """
    q = value if isinstance(value, Fraction) else Fraction(float(value)).limit_denominator(4096)
    return str(q)


def _plot_pair_label(value: Any) -> str:
    return f"({_plot_fraction_label(value[0])}, {_plot_fraction_label(value[1])})"


def _plot_validate_inputs(geometry_data: dict, runs: list[dict],
                          examples: dict, fitness_grid: list[list[float]]) -> tuple[dict, list[dict], list[list[float]]]:
    """Detecta errores de contrato antes de crear archivos parciales.

    Las comprobaciones son de estructura y de valores dibujables. La comprobación
    matemática del artículo corresponde al verificador racional del programa.
    """
    if not isinstance(geometry_data, dict) or not isinstance(examples, dict):
        raise TypeError("geometry_data y examples deben ser diccionarios.")
    geom = {key: _plot_point(geometry_data[key], key)
            for key in ("A", "B", "C", "O", "H", "N")}
    for key in ("R2", "r2"):
        geom[key] = _plot_float(geometry_data[key], key)
        if geom[key] <= 0:
            raise ValueError(f"{key} debe ser positivo para dibujar la circunferencia.")
    if not isinstance(geometry_data.get("points"), dict):
        raise ValueError("geometry_data['points'] debe contener los nueve puntos etiquetados.")
    labels = ("Ma", "Mb", "Mc", "Da", "Db", "Dc", "Ea", "Eb", "Ec")
    geom["points"] = {label: _plot_point(geometry_data["points"][label], label) for label in labels}

    if not isinstance(runs, list) or not runs:
        raise ValueError("Se necesita al menos una corrida real para dibujar resultados.")
    clean_runs = []
    for index, run in enumerate(runs):
        if not isinstance(run, dict):
            raise ValueError(f"La corrida {index} debe ser un diccionario.")
        if not isinstance(run.get("accepted"), bool):
            raise ValueError(f"La corrida {index} requiere accepted de tipo bool.")
        history = run.get("history")
        if not isinstance(history, list) or not history:
            raise ValueError(f"La corrida {index} no tiene historial para graficar.")
        clean_history = []
        previous_generation = -1
        for row in history:
            generation = row["generation"]
            if isinstance(generation, bool) or not isinstance(generation, int) or generation <= previous_generation:
                raise ValueError("Las generaciones deben ser enteros no negativos en orden estrictamente creciente.")
            previous_generation = generation
            item = {"generation": generation}
            for key in ("best_J", "mean_J", "diversity", "exact_count"):
                item[key] = _plot_float(row[key], f"corrida {index}, generación {generation}, {key}")
                if item[key] < 0:
                    raise ValueError(f"{key} no puede ser negativo.")
            for key in ("diversity", "exact_count"):
                if not item[key].is_integer() or item[key] > 100:
                    raise ValueError(f"{key} debe ser un conteo entero entre 0 y 100 para este protocolo.")
            clean_history.append(item)
        clean_runs.append({"seed": run["seed"], "accepted": run["accepted"],
                           "final_center": _plot_point(run["final_center"], f"centro final de corrida {index}"),
                           "history": clean_history})

    if not isinstance(fitness_grid, list) or len(fitness_grid) != 256:
        raise ValueError("fitness_grid debe tener 256 filas v y 256 columnas u.")
    grid = []
    for v, row in enumerate(fitness_grid):
        if not isinstance(row, list) or len(row) != 256:
            raise ValueError(f"La fila v={v} debe tener 256 valores de J.")
        clean_row = [_plot_float(value, f"fitness_grid[{v}][{u}]") for u, value in enumerate(row)]
        if any(value < 0 for value in clean_row):
            raise ValueError("La rejilla de J no puede contener valores negativos.")
        grid.append(clean_row)
    return geom, clean_runs, grid


def _plot_save_pair(fig: Any, output_dir: Path, stem: str) -> list[Path]:
    """Usa el mismo lienzo para que PNG y SVG contengan idéntica información."""
    png = output_dir / (stem + ".png")
    svg = output_dir / (stem + ".svg")
    fig.savefig(png, dpi=300, facecolor="white", bbox_inches="tight", pad_inches=0.18)
    fig.savefig(svg, facecolor="white", bbox_inches="tight", pad_inches=0.18)
    return [png, svg]


def _plot_geometry(plt: Any, Circle: Any, Line2D: Any, geom: dict) -> Any:
    """Figura 1: las posiciones proceden de la construcción geométrica recibida."""
    fig, ax = plt.subplots(figsize=(12.4, 8.6))
    fig.subplots_adjust(left=0.07, right=0.73, top=0.88, bottom=0.13)
    fig.suptitle("Triángulo y circunferencia de los nueve puntos", fontsize=18, color=_PLOT_PURPLE, y=0.975)
    vertices = [geom[key] for key in ("A", "B", "C", "A")]
    ax.plot([p[0] for p in vertices], [p[1] for p in vertices], color=_PLOT_GRAY, linewidth=2.1, zorder=1)
    radius = math.sqrt(geom["r2"])
    ax.add_patch(Circle(geom["N"], radius, fill=False, color=_PLOT_PURPLE, linewidth=2.5, zorder=2))

    # Los desplazamientos solo separan rótulos: no desplazan ningún punto.
    offsets = {"Ma": (10, 9), "Mb": (-30, 9), "Mc": (9, -23),
               "Da": (10, 12), "Db": (-33, -12), "Dc": (-15, -27),
               "Ea": (-29, -21), "Eb": (10, -22), "Ec": (-31, 13),
               "A": (-17, -20), "B": (11, -16), "C": (0, 15),
               "O": (12, 12), "H": (-23, -21), "N": (0, 15)}
    groups = (("M", "o", _PLOT_TEAL), ("D", "^", _PLOT_ORANGE), ("E", "s", _PLOT_BLUE))
    for prefix, marker, color in groups:
        for suffix in "abc":
            key = prefix + suffix
            p = geom["points"][key]
            ax.scatter(*p, s=100, marker=marker, color=color, edgecolors="white", linewidths=1, zorder=5)
            ax.annotate(f"${prefix}_{{{suffix}}}$", p, xytext=offsets[key], textcoords="offset points",
                        fontsize=13, color=color, ha="left" if offsets[key][0] > 0 else "right",
                        annotation_clip=False)
    for key in ("A", "B", "C"):
        p = geom[key]
        ax.scatter(*p, s=40, color=_PLOT_INK, zorder=6)
        ax.annotate(key, p, xytext=offsets[key], textcoords="offset points", fontsize=14,
                    color=_PLOT_INK, weight="bold", annotation_clip=False)
    for key, marker, color, size in (("O", "+", _PLOT_INK, 140),
                                     ("H", "x", _PLOT_INK, 110),
                                     ("N", "*", _PLOT_PURPLE, 240)):
        ax.scatter(*geom[key], marker=marker, color=color, s=size, linewidths=2.0, zorder=7)
        ax.annotate(key, geom[key], xytext=offsets[key], textcoords="offset points", fontsize=14,
                    color=color, weight="bold", annotation_clip=False)

    all_points = [geom[key] for key in ("A", "B", "C", "O", "H", "N")] + list(geom["points"].values())
    xs = [p[0] for p in all_points] + [geom["N"][0] - radius, geom["N"][0] + radius]
    ys = [p[1] for p in all_points] + [geom["N"][1] - radius, geom["N"][1] + radius]
    padding = 0.16 * max(max(xs) - min(xs), max(ys) - min(ys), 1)
    ax.set_xlim(min(xs) - padding, max(xs) + padding)
    ax.set_ylim(min(ys) - padding, max(ys) + padding)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel("Coordenada x")
    ax.set_ylabel("Coordenada y")
    ax.grid(color="#E8E4ED", linewidth=0.6, zorder=0)
    handles = [Line2D([], [], marker=m, color="none", markerfacecolor=c, markeredgecolor="white", markersize=10, label=label)
               for m, c, label in (("o", _PLOT_TEAL, "Puntos medios de lados"),
                                    ("^", _PLOT_ORANGE, "Pies de las alturas"),
                                    ("s", _PLOT_BLUE, "Puntos medios con H"))]
    handles += [Line2D([], [], marker=marker, color=color, linestyle="none", markersize=10, label=label)
                for marker, color, label in (("+", _PLOT_INK, "O  Circuncentro"),
                                             ("x", _PLOT_INK, "H  Ortocentro"),
                                             ("*", _PLOT_PURPLE, "N  Centro de nueve puntos"))]
    ax.legend(handles=handles, loc="upper left", bbox_to_anchor=(1.015, 1.0), frameon=False,
              handletextpad=0.7, labelspacing=1.15, fontsize=10.5)
    fig.text(0.77, 0.37,
             "Centro calculado\n" + "N = " + _plot_pair_label(geom["N"]) + "\n\n"
             + "Radio al cuadrado\n" + "r² = " + _plot_fraction_label(geom["r2"]),
             ha="left", va="top", color=_PLOT_INK, fontsize=12, linespacing=1.5)
    fig.text(0.07, 0.045, "   ".join(key + " = " + _plot_pair_label(geom[key]) for key in ("A", "B", "C")),
             fontsize=11, color=_PLOT_GRAY)
    return fig


def _plot_cycle(plt: Any, FancyBboxPatch: Any, runs: list[dict]) -> Any:
    """Figura 2: el presupuesto se comprueba después de evaluar la población."""
    fig, ax = plt.subplots(figsize=(15.8, 8.8))
    fig.subplots_adjust(left=0.025, right=0.975, top=0.88, bottom=0.115)
    fig.suptitle("Ciclo de las siete etapas del algoritmo genético", color=_PLOT_PURPLE, fontsize=18, y=0.97)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    budgets = sorted({run["history"][-1]["generation"] for run in runs})
    budget_text = f"G = {budgets[0]}" if len(budgets) == 1 else "G = presupuesto fijado"
    boxes = {
        "init": (0.015, 0.735, "1. Inicialización\n100 individuos; g = 0"),
        "evaluate": (0.015, 0.405, "2. Evaluación y registro\nJ mínimo, medio, diversidad\ny cantidad de soluciones exactas"),
        "terminate": (0.355, 0.405, "7. Terminación\n¿Se alcanzó G?\n" + budget_text),
        "accept": (0.355, 0.735, "Comprobar nueve puntos\ny condiciones de construcción\nComunicar aceptación o rechazo"),
        "select": (0.695, 0.405, "3. Selección por torneo\n98 torneos de dos individuos\n49 parejas"),
        "cross": (0.695, 0.075, "4. Cruce de un punto\nProbabilidad 0.90\nUno de los 15 cortes internos"),
        "mutate": (0.355, 0.075, "5. Mutación\nProbabilidad 0.01 por bit\n98 hijos; 16 bits por hijo"),
        "replace": (0.015, 0.075, "6. Reemplazo elitista\n2 élites intactas + 98 hijos\ng ← g + 1"),
    }
    width, height = 0.29, 0.22
    for key, (x, y, label) in boxes.items():
        edge = _PLOT_TEAL if key == "accept" else _PLOT_PURPLE
        fill = "#EFF8F8" if key == "accept" else _PLOT_LIGHT
        ax.add_patch(FancyBboxPatch((x, y), width, height, boxstyle="round,pad=0.007,rounding_size=0.012",
                                   linewidth=1.8, edgecolor=edge, facecolor=fill))
        ax.text(x + width / 2, y + height / 2, label, ha="center", va="center",
                fontsize=12.6, linespacing=1.45, color=_PLOT_INK)

    def connect(start, end, label=None, label_at=None):
        # shrink evita que la punta tape el borde de la caja de destino.
        ax.annotate("", xy=end, xytext=start,
                    arrowprops={"arrowstyle": "-|>", "mutation_scale": 16, "linewidth": 1.8,
                                "color": _PLOT_GRAY, "shrinkA": 3, "shrinkB": 3})
        if label:
            ax.text(*label_at, label, fontsize=12, color=_PLOT_INK, ha="center", va="center")

    connect((0.16, 0.735), (0.16, 0.625))
    connect((0.305, 0.515), (0.355, 0.515))
    connect((0.645, 0.515), (0.695, 0.515), "No", (0.670, 0.558))
    connect((0.50, 0.625), (0.50, 0.735), "Sí", (0.538, 0.680))
    connect((0.84, 0.405), (0.84, 0.295))
    connect((0.695, 0.185), (0.645, 0.185))
    connect((0.355, 0.185), (0.305, 0.185))
    connect((0.16, 0.295), (0.16, 0.405))
    fig.text(0.5, 0.058, "Encontrar J = 0 no interrumpe el ciclo. Cada población se evalúa antes de revisar el presupuesto.",
             fontsize=12, ha="center", color=_PLOT_GRAY)
    return fig


def _plot_manual_details(code: int) -> dict:
    """Recalcula los números ilustrativos; no consulta ni altera ninguna corrida."""
    u, v = code >> 8, code & 255
    ns = [(u - x) ** 2 + (v - y) ** 2 - 5120 for x, y in ((160, 96), (32, 96), (128, 0))]
    return {"code": code, "u": u, "v": v, "Q": (Fraction(u, 64), Fraction(v, 64)),
            "J": Fraction(sum(n * n for n in ns), 1048576), "bits": f"{code:016b}"}


def _plot_operators(plt: Any, FancyBboxPatch: Any, Rectangle: Any, examples: dict) -> Any:
    """Figura 3: usa los progenitores del artículo y operaciones binarias reales.

    Si examples incluye la estructura figure3 del contrato de revisión, contrasta
    sus J con los calculados. El ejemplo permanece independiente del estado RNG.
    """
    parent_codes = (0x6020, 0x2040)
    cut = 8
    tail_mask = (1 << (16 - cut)) - 1
    first = (parent_codes[0] & ~tail_mask) | (parent_codes[1] & tail_mask)
    second = (parent_codes[1] & ~tail_mask) | (parent_codes[0] & tail_mask)
    mutant = second ^ (1 << (16 - 10))
    data = [_plot_manual_details(code) for code in (*parent_codes, first, second, mutant)]
    supplied = examples.get("figure3", {})
    if isinstance(supplied, dict) and isinstance(supplied.get("children"), list):
        for given, calculated in zip(supplied["children"], data[2:4]):
            if isinstance(given, dict) and "J" in given and Fraction(str(given["J"])) != calculated["J"]:
                raise ValueError("El J del ejemplo de cruce recibido no coincide con el cálculo binario.")

    fig, ax = plt.subplots(figsize=(16.2, 8.4))
    fig.subplots_adjust(left=0.025, right=0.975, top=0.88, bottom=0.12)
    fig.suptitle("Cruce de un punto y mutación ilustrativa", fontsize=18, color=_PLOT_PURPLE, y=0.97)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    width, height = 0.286, 0.24

    def card(x, y, title, record, colors, mutated_bit=None):
        ax.text(x + width / 2, y + height + 0.044, title, fontsize=14.5, weight="bold",
                ha="center", va="bottom", color=_PLOT_PURPLE)
        ax.add_patch(FancyBboxPatch((x, y), width, height, boxstyle="round,pad=0.007,rounding_size=0.012",
                                   facecolor="white", edgecolor=_PLOT_PURPLE, linewidth=1.7))
        # Cada carácter tiene su posición: el color muestra el progenitor de origen.
        start = x + 0.015
        step = 0.0151
        for index, bit in enumerate(record["bits"]):
            xpos = start + index * step + (0.013 if index >= 8 else 0)
            if index + 1 == mutated_bit:
                ax.add_patch(Rectangle((xpos - 0.0064, y + 0.145), 0.0140, 0.057,
                                       facecolor="#FCE3B4", edgecolor=_PLOT_ORANGE, linewidth=0.9))
            color = colors[0] if index < 8 else colors[1]
            ax.text(xpos, y + 0.174, bit, fontfamily="DejaVu Sans Mono", fontsize=17.3,
                    ha="center", va="center", color=color, weight="bold")
        bar_x = start + 7.5 * step + 0.0065
        ax.plot([bar_x, bar_x], [y + 0.141, y + 0.207], color=_PLOT_GRAY, linewidth=1)
        ax.text(x + width / 2, y + 0.094, "Q = " + _plot_pair_label(record["Q"]),
                fontsize=12.3, ha="center", color=_PLOT_INK)
        ax.text(x + width / 2, y + 0.034, "J = " + str(record["J"]),
                fontsize=13.5, ha="center", color=_PLOT_INK, weight="bold")

    card(0.014, 0.605, "Progenitor I₁", data[0], (_PLOT_PURPLE, _PLOT_PURPLE))
    card(0.014, 0.115, "Progenitor I₂", data[1], (_PLOT_TEAL, _PLOT_TEAL))
    card(0.355, 0.605, "Hijo 1", data[2], (_PLOT_PURPLE, _PLOT_TEAL))
    card(0.355, 0.115, "Hijo 2", data[3], (_PLOT_TEAL, _PLOT_PURPLE))
    card(0.696, 0.115, "Hijo 2 tras mutación", data[4], (_PLOT_TEAL, _PLOT_PURPLE), mutated_bit=10)
    for start, end in (((0.305, 0.725), (0.349, 0.725)),
                       ((0.305, 0.235), (0.349, 0.235)),
                       ((0.646, 0.235), (0.690, 0.235))):
        ax.annotate("", xy=end, xytext=start,
                    arrowprops={"arrowstyle": "-|>", "mutation_scale": 17, "color": _PLOT_GRAY, "linewidth": 1.8})
    ax.text(0.495, 0.535, "Corte después del bit 8", fontsize=13, ha="center", color=_PLOT_INK)
    ax.text(0.495, 0.475, "Los colores identifican el progenitor de cada bloque.", fontsize=10.5,
            ha="center", color=_PLOT_GRAY)
    ax.text(0.839, 0.805, "Mutación del bit 10", fontsize=14.3, weight="bold", ha="center", color=_PLOT_TEAL)
    ax.text(0.839, 0.690, "0 → 1\nv: 32 → 96\nqᵧ: 1/2 → 3/2", fontsize=15.0,
            ha="center", va="center", linespacing=1.6, color=_PLOT_INK)
    ax.text(0.839, 0.485, "El error aumenta:\n251 → 315", fontsize=12.5,
            ha="center", color=_PLOT_ORANGE, linespacing=1.5)
    fig.text(0.5, 0.048, "Ejemplo con corte e inversión fijados para explicar las operaciones. En las corridas ambos se sortean.",
             ha="center", fontsize=11.5, color=_PLOT_GRAY)
    return fig


def _plot_convergence(plt: Any, Line2D: Any, runs: list[dict]) -> Any:
    """Figura 4: cada curva procede de un historial recibido, incluida P(0)."""
    fig, axes = plt.subplots(2, 2, figsize=(14.4, 10.2))
    fig.subplots_adjust(left=0.085, right=0.97, top=0.83, bottom=0.11, hspace=0.33, wspace=0.24)
    fig.suptitle(f"Evolución de {len(runs)} corridas genéticas", fontsize=18, color=_PLOT_PURPLE, y=0.97)
    fields = (("best_J", "Mejor error J", "J mínimo"),
              ("mean_J", "Error medio de la población", "J medio"),
              ("diversity", "Diversidad de la población", "Cromosomas distintos"),
              ("exact_count", "Presencia de soluciones exactas", "Individuos con J = 0"))
    last_generation = max(run["history"][-1]["generation"] for run in runs)
    for ax, (field, title, ylabel) in zip(axes.flat, fields):
        by_generation = defaultdict(list)
        for run in runs:
            xs = [row["generation"] for row in run["history"]]
            ys = [row[field] for row in run["history"]]
            color = _PLOT_TEAL if run["accepted"] else _PLOT_PURPLE
            ax.plot(xs, ys, color=color, alpha=0.22, linewidth=0.75, zorder=2)
            for x, y in zip(xs, ys):
                by_generation[x].append(y)
        gx = sorted(by_generation)
        gy = [median(by_generation[g]) for g in gx]
        ax.plot(gx, gy, color=_PLOT_INK, linewidth=2.1, zorder=5)
        ax.set_title(title, fontsize=13, color=_PLOT_INK, pad=10)
        ax.set_xlabel("Generación g")
        ax.set_ylabel(ylabel)
        ax.set_xlim(0, max(last_generation, 1))
        if field.endswith("_J"):
            # symlog muestra J=0; una escala logarítmica ordinaria lo ocultaría.
            ax.set_yscale("symlog", linthresh=0.001, linscale=0.8)
            ax.set_ylim(bottom=-0.00015)
            ax.axhline(0, color="#A9A1B1", linewidth=0.6, zorder=1)
        else:
            ax.set_ylim(-2, 102)
            ax.set_yticks([0, 20, 40, 60, 80, 100])
        ax.grid(color="#E6E1EB", linewidth=0.65, alpha=0.9)
        ax.spines[["top", "right"]].set_visible(False)
    accepted = sum(run["accepted"] for run in runs)
    handles = [Line2D([], [], color=_PLOT_TEAL, linewidth=1.6, label=f"Certificadas: {accepted}"),
               Line2D([], [], color=_PLOT_PURPLE, linewidth=1.6, label=f"No certificadas: {len(runs) - accepted}"),
               Line2D([], [], color=_PLOT_INK, linewidth=2.1, label="Mediana por generación")]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.53, 0.925), ncol=3,
               frameon=False, fontsize=11)
    fig.text(0.5, 0.040, "Cada línea fina representa una corrida. Los paneles de J usan symlog, con una zona lineal que conserva el cero.",
             ha="center", fontsize=10.7, color=_PLOT_GRAY)
    return fig


def _plot_landscape(plt: Any, LinearSegmentedColormap: Any, Line2D: Any,
                    runs: list[dict], grid: list[list[float]]) -> Any:
    """Figura 5: transforma J solo para colorear y conserva centros observados."""
    log_grid = [[math.log1p(value) for value in row] for row in grid]
    minimum = min(min(row) for row in grid)
    minima = [(u / 64, v / 64) for v, row in enumerate(grid) for u, value in enumerate(row) if value == minimum]
    # En este problema hay un único mínimo. La selección no usa el dato conocido N.
    # Si una futura entrada contiene varios mínimos, se muestran todos.
    finals = Counter((run["final_center"][0], run["final_center"][1], run["accepted"]) for run in runs)
    fig = plt.figure(figsize=(15.6, 8.4))
    spec = fig.add_gridspec(1, 3, width_ratios=[1.15, 1, 0.045], left=0.065, right=0.955,
                           top=0.84, bottom=0.22, wspace=0.23)
    ax_full, ax_zoom, cax = (fig.add_subplot(spec[0, i]) for i in range(3))
    fig.suptitle("Paisaje del error y centros finales de las corridas", fontsize=18, color=_PLOT_PURPLE, y=0.965)
    colors = ["#FFFFFF", "#E5DCF2", "#A77EC6", "#5F529B", "#223F70"]
    cmap = LinearSegmentedColormap.from_list("nueve_puntos_error", colors)
    # Las celdas se centran exactamente en u/64 y v/64. origin='lower' evita
    # invertir el eje vertical respecto de la interpretación geométrica.
    half_step = 1 / 128
    extent = (-half_step, 255 / 64 + half_step, -half_step, 255 / 64 + half_step)
    vmax = max(max(row) for row in log_grid)
    image = None
    for ax in (ax_full, ax_zoom):
        image = ax.imshow(log_grid, origin="lower", extent=extent, cmap=cmap, vmin=0,
                          vmax=vmax if vmax > 0 else 1, interpolation="nearest", aspect="equal")
        for (x, y, accepted), count in sorted(finals.items()):
            color = _PLOT_TEAL if accepted else _PLOT_ORANGE
            ax.scatter(x, y, s=72 + 8 * count, marker="o", facecolors="none", edgecolors=color,
                       linewidths=1.7, zorder=5)
        ax.scatter([p[0] for p in minima], [p[1] for p in minima], s=150, marker="*",
                   color=_PLOT_GOLD, edgecolors=_PLOT_INK, linewidths=0.75, zorder=7)
        ax.set_xlabel("qₓ = u / 64")
        ax.set_ylabel("qᵧ = v / 64")
        ax.set_axisbelow(False)
    ax_full.set_title("65,536 centros representables", fontsize=13, pad=12)
    ax_full.set_xlim(extent[:2])
    ax_full.set_ylim(extent[2:])
    ax_zoom.set_title("Detalle de los centros finales", fontsize=13, pad=12)
    relevant = list(minima) + [(x, y) for x, y, _ in finals]
    xs, ys = [p[0] for p in relevant], [p[1] for p in relevant]
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1 / 64)
    padding = max(4 / 64, span * 0.28)
    ax_zoom.set_xlim(max(extent[0], min(xs) - padding), min(extent[1], max(xs) + padding))
    ax_zoom.set_ylim(max(extent[2], min(ys) - padding), min(extent[3], max(ys) + padding))
    ax_zoom.grid(color="#CDC4D7", linewidth=0.5, alpha=0.7)

    # Las frecuencias se calculan de las corridas; no se copia el resumen publicado.
    # Rótulos alternados y conectados permiten distinguir vecinos a distancia 1/64.
    center_x = (min(xs) + max(xs)) / 2
    center_y = (min(ys) + max(ys)) / 2
    levels = Counter()
    for index, ((x, y, accepted), count) in enumerate(sorted(finals.items(), key=lambda item: (item[0][1], item[0][0]))):
        # Cada etiqueta se aleja del centro del grupo. Así los cuatro vecinos
        # ocupan cuadrantes distintos y ninguna caja oculta la estrella del óptimo.
        sx = 1 if x >= center_x else -1
        sy = 1 if y >= center_y else -1
        level = levels[(sx, sy)]
        levels[(sx, sy)] += 1
        dx, dy = sx * (32 + 5 * level), sy * (39 + 27 * level)
        label = f"{count} corrida{'s' if count != 1 else ''}\nQ = {_plot_pair_label((x, y))}"
        ax_zoom.annotate(label, (x, y), xytext=(dx, dy), textcoords="offset points",
                         ha="left" if dx > 0 else "right", va="center", fontsize=9.4,
                         color=_PLOT_INK, bbox={"boxstyle": "round,pad=0.3", "fc": "white", "ec": "#D5CDDF", "alpha": 0.95},
                         arrowprops={"arrowstyle": "-", "color": _PLOT_GRAY, "linewidth": 0.7}, zorder=9)
    bar = fig.colorbar(image, cax=cax)
    bar.set_label("ln(1 + J)", labelpad=10)
    handles = [Line2D([], [], marker="*", markerfacecolor=_PLOT_GOLD, markeredgecolor=_PLOT_INK,
                      color="none", markersize=12, label=f"Mínimo de la rejilla: J = {minimum:g}"),
               Line2D([], [], marker="o", markerfacecolor="none", markeredgecolor=_PLOT_TEAL,
                      color="none", markersize=10, label="Centro final certificado"),
               Line2D([], [], marker="o", markerfacecolor="none", markeredgecolor=_PLOT_ORANGE,
                      color="none", markersize=10, label="Centro final no certificado")]
    fig.legend(handles=handles, loc="lower center", bbox_to_anchor=(0.50, 0.108), ncol=3, frameon=False, fontsize=10.5)
    fig.text(0.5, 0.055, "El color usa ln(1 + J) solo para visualizar. Las coordenadas y frecuencias finales proceden de las corridas ejecutadas.",
             fontsize=10.5, ha="center", color=_PLOT_GRAY)
    return fig


def generate_figures(output_dir: Any, geometry_data: dict, runs: list[dict],
                     examples: dict, fitness_grid: list[list[float]]) -> list[Path]:
    """Genera las cinco figuras y devuelve sus diez rutas, PNG y SVG.

    Parámetros
    ----------
    output_dir:
        Directorio de salida, creado si todavía no existe.
    geometry_data:
        A, B, C, O, H y N son pares numéricos; R2 y r2 son positivos.
        points contiene Ma, Mb, Mc, Da, Db, Dc, Ea, Eb y Ec.
    runs:
        Lista de corridas reales. Cada diccionario contiene seed, final_center,
        accepted y history. Las filas del historial incluyen generation, best_J,
        mean_J, diversity y exact_count. Se admiten Fraction en los campos de J.
    examples:
        Datos ilustrativos del orquestador. Se admite el diccionario figure3 del
        contrato de ejemplos para contrastar los J, si se proporciona.
    fitness_grid:
        Lista de 256 filas v por 256 columnas u, con J(u/64, v/64).

    Excepciones
    -----------
    ImportError:
        Matplotlib no está disponible. El orquestador decide si omite las figuras
        o comunica cómo instalar la dependencia; este componente no la instala.
    ValueError, TypeError, KeyError:
        Los datos recibidos no cumplen el contrato declarado.

    Notas
    -----
    Se fuerza el backend Agg antes de importar pyplot para ejecutarse sin ventana.
    Todas las figuras se cierran, incluso si falla la escritura de un archivo.
    La conversión a float solo pertenece a la presentación; el cálculo exacto y
    las decisiones científicas deben haberse realizado antes de llamar aquí.
    """
    geom, clean_runs, grid = _plot_validate_inputs(geometry_data, runs, examples, fitness_grid)
    try:
        import matplotlib
        matplotlib.use("Agg", force=True)
        import matplotlib.pyplot as plt
        from matplotlib.colors import LinearSegmentedColormap
        from matplotlib.lines import Line2D
        from matplotlib.patches import Circle, FancyBboxPatch, Rectangle
    except ImportError as exc:
        raise ImportError("No se generaron figuras porque falta Matplotlib. Instale matplotlib explícitamente o ejecute sin figuras.") from exc

    directory = Path(output_dir)
    directory.mkdir(parents=True, exist_ok=True)
    saved = []
    style = {"font.family": "DejaVu Sans", "font.size": 11, "axes.labelcolor": _PLOT_INK,
             "text.color": _PLOT_INK, "axes.edgecolor": "#B0A7BA", "axes.titleweight": "normal",
             "figure.facecolor": "white", "axes.facecolor": "white", "savefig.facecolor": "white",
             "svg.fonttype": "none", "axes.unicode_minus": True}
    with plt.rc_context(style):
        builders = [
            ("01_triangulo_nueve_puntos", lambda: _plot_geometry(plt, Circle, Line2D, geom)),
            ("02_ciclo_siete_etapas", lambda: _plot_cycle(plt, FancyBboxPatch, clean_runs)),
            ("03_cruce_y_mutacion", lambda: _plot_operators(plt, FancyBboxPatch, Rectangle, examples)),
            ("04_convergencia_y_diversidad", lambda: _plot_convergence(plt, Line2D, clean_runs)),
            ("05_paisaje_error_y_centros", lambda: _plot_landscape(plt, LinearSegmentedColormap, Line2D, clean_runs, grid)),
        ]
        for stem, builder in builders:
            fig = None
            try:
                fig = builder()
                saved.extend(_plot_save_pair(fig, directory, stem))
            finally:
                if fig is not None:
                    plt.close(fig)
    return saved


# ============================================================================
# EXPERIMENTOS, EXPORTACIÓN Y EJECUCIÓN DEL PROGRAMA COMPLETO
# Este bloque conecta las funciones anteriores con las secciones del artículo.
# Las tablas se construyen con resultados calculados; la referencia publicada
# se conserva únicamente en el apartado de comparación.
# ============================================================================


def np_json_ready(value):
    """Convierte objetos exactos sin perder sus numeradores y denominadores.

    Una fracción se escribe como cadena, por ejemplo "3/2"; puede recuperarse
    con Fraction(cadena). Los decimales se reservan para gráficas y columnas
    informativas. No se utiliza esta conversión para decidir aceptación.
    """
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, Point):
        return {"x": str(value.x), "y": str(value.y)}
    if is_dataclass(value):
        return np_json_ready(asdict(value))
    if isinstance(value, dict):
        return {str(key): np_json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [np_json_ready(item) for item in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    raise TypeError(f"Objeto no serializable: {type(value).__name__}")


def np_save_json(path, data):
    """Guarda JSON legible en UTF-8; no permite NaN ni infinitos silenciosos."""
    Path(path).write_text(
        json.dumps(np_json_ready(data), ensure_ascii=False, indent=2, allow_nan=False),
        encoding="utf-8",
    )


def np_save_csv(path, rows, fieldnames=None):
    """CSV compatible con Python y hojas de cálculo, con fracciones textuales.

    UTF-8 con BOM facilita la lectura de acentos en Excel para Windows. Una
    celda que contiene una lista/diccionario se escribe como JSON compacto;
    los valores escalares conservan su representación decimal o racional.
    """
    rows = list(rows)
    if fieldnames is None:
        fieldnames = list(dict.fromkeys(key for row in rows for key in row))
    with Path(path).open("w", encoding="utf-8-sig", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, extrasaction="raise")
        writer.writeheader()
        for row in rows:
            converted = {}
            for key, value in row.items():
                if isinstance(value, (dict, tuple, list)):
                    value = json.dumps(np_json_ready(value), ensure_ascii=False)
                elif isinstance(value, Fraction):
                    value = str(value)
                converted[key] = value
            writer.writerow(converted)


def np_chromosome_text(code):
    """Muestra los dos bloques de ocho bits sin modificar el cromosoma."""
    bits = f"{code:016b}"
    return bits[:8] + "|" + bits[8:]


def np_manual_examples(model, configuration):
    """Recalcula la tabla 2 y la figura 3 sin consumir números aleatorios.

    Los cuatro candidatos son entradas de un ejemplo del artículo. Sus errores
    NO se copian de una tabla: evaluate y residual_numerators vuelven a obtener
    los valores. Estos cromosomas nunca se incorporan a P(0) de las corridas.
    """
    def candidate(name, code):
        center = model.decode(code)
        residues = tuple(Fraction(n, model.residual_denominator)
                         for n in model.residual_numerators(code))
        return {
            "individuo": name, "codigo": code,
            "cromosoma": np_chromosome_text(code),
            "qx": center[0], "qy": center[1],
            "e_Ma": residues[0], "e_Mb": residues[1], "e_Mc": residues[2],
            "K_entero": model.evaluate(code), "J_exacto": model.j_value(code),
            "J_decimal": float(model.j_value(code)),
        }

    parents = [candidate(name, (u << 8) | v) for name, u, v in (
        ("I1", 96, 32), ("I2", 32, 64), ("I3", 0, 0), ("I4", 192, 192)
    )]
    # El corte de la figura es después del octavo bit. Una máscara de ocho
    # unos conserva el sufijo; el complemento dentro de 16 bits conserva el
    # prefijo. Esta cuenta es la misma operación binaria que utiliza el GA.
    cut = 8
    low_mask = (1 << (16 - cut)) - 1
    high_mask = 0xFFFF ^ low_mask
    p1, p2 = parents[0]["codigo"], parents[1]["codigo"]
    child1 = (p1 & high_mask) | (p2 & low_mask)
    child2 = (p2 & high_mask) | (p1 & low_mask)
    # La posición 10 se cuenta desde la izquierda, empezando en uno. Su máscara
    # es 1 << (16-10). XOR invierte exclusivamente ese bit del segundo hijo.
    mutation_position = 10
    altered = child2 ^ (1 << (16 - mutation_position))
    operations = [candidate("Hijo 1", child1), candidate("Hijo 2", child2),
                  candidate("Hijo 2 mutado", altered)]
    offspring = configuration.population_size - configuration.elitism
    return {
        "table2_rows": parents,
        "figure3_rows": operations,
        "cut_after_bit": cut, "mutation_position_from_left": mutation_position,
        "tournaments_illustrated": [
            {"candidatos": ["I1", "I3"], "ganador": min((parents[0], parents[2]), key=lambda x: x["K_entero"])["individuo"]},
            {"candidatos": ["I2", "I4"], "ganador": min((parents[1], parents[3]), key=lambda x: x["K_entero"])["individuo"]},
        ],
        "expected_crossed_pairs": offspring / 2 * configuration.crossover_probability,
        "expected_bit_mutations": offspring * 16 * configuration.mutation_probability,
        "probability_child_changes": 1 - (1 - configuration.mutation_probability) ** 16,
        "note": "Ejemplos fijados para explicar operadores; no son una corrida ni una población inicial.",
    }


def np_enumerate_encoding(model, output_directory):
    """Sección 3.2: inspecciona todos los centros representables.

    Esta enumeración es un experimento separado. No entrega sus mejores
    cromosomas al algoritmo genético ni sustituye las 1,503,000 evaluaciones
    poblacionales. La matriz que devuelve usa grid[v][u], para dibujar x en
    columnas e y en filas. Las decisiones se basan en K entero, no en la imagen.
    """
    grid = [[0.0 for _ in range(256)] for _ in range(256)]
    zeros = []
    best_k = None
    best_codes = []
    count = 0
    with gzip.open(Path(output_directory) / "rejilla_65536_centros.csv.gz", "wt",
                   encoding="utf-8", newline="", compresslevel=6) as stream:
        writer = csv.writer(stream)
        writer.writerow(["codigo_hex", "u", "v", "qx_exacto", "qy_exacto", "K_entero", "J_exacto", "J_decimal"])
        for code in range(1 << 16):
            u, v = code >> 8, code & 255
            k = model.evaluate(code)
            j = model.k_to_j(k)
            qx, qy = model.decode(code)
            count += 1
            grid[v][u] = float(j)
            writer.writerow([f"{code:04x}", u, v, str(qx), str(qy), k, str(j), float(j)])
            if k == 0:
                zeros.append(code)
            if best_k is None or k < best_k:
                best_k, best_codes = k, [code]
            elif k == best_k:
                best_codes.append(code)
    return {
        "codes_evaluated": count,
        "zero_count": len(zeros), "zero_codes": zeros,
        "zero_centers": [model.decode(code) for code in zeros],
        "minimum_K": best_k, "minimum_J": model.k_to_j(best_k),
        "minimum_codes": best_codes,
        "note": "Enumeración independiente; ninguna de sus soluciones se inserta en el GA.",
    }, grid


def np_summarize_runs(runs):
    """Agrega únicamente las observaciones devueltas por run_ga."""
    n = len(runs)
    successful = [run for run in runs if run["accepted"]]
    failed = [run for run in runs if not run["accepted"]]
    firsts = [run["first_zero_generation"] for run in successful]
    failure_centers = {}
    for run in failed:
        center = "(" + ", ".join(str(x) for x in run["final_center"]) + ")"
        failure_centers.setdefault(center, {"seeds": [], "J_exact": run["best_J"]})["seeds"].append(run["seed"])
    return {
        "runs": n, "successes": len(successful), "failures": len(failed),
        "success_fraction": Fraction(len(successful), n),
        "success_percent": 100 * len(successful) / n,
        "total_evaluations": sum(run["evaluations"] for run in runs),
        "total_population_records": sum(len(run["history"]) for run in runs),
        "initial_exact_individuals": sum(run["history"][0]["exact_count"] for run in runs),
        "first_zero_min": min(firsts) if firsts else None,
        "first_zero_max": max(firsts) if firsts else None,
        "first_zero_median": statistics.median(firsts) if firsts else None,
        "initial_diversity_mean": Fraction(sum(run["history"][0]["diversity"] for run in runs), n),
        "final_diversity_mean": Fraction(sum(run["history"][-1]["diversity"] for run in runs), n),
        "failed_J_min": min((run["best_J"] for run in failed), default=None),
        "failed_J_max": max((run["best_J"] for run in failed), default=None),
        "successful_seeds": [run["seed"] for run in successful],
        "failed_seeds": [run["seed"] for run in failed],
        "failure_centers": failure_centers,
        "minimum_never_increased": all(
            all(current["best_k"] <= previous["best_k"]
                for previous, current in zip(run["history"], run["history"][1:]))
            for run in runs
        ),
    }


def np_compare_article(summary, bank, config, seeds):
    """Confronta referencia publicada y ejecución, sin modificar esta última.

    Las constantes publicadas aparecen SOLO en este contraste o en pruebas
    de resultados conocidos. No intervienen en la selección, el cruce, la
    mutación, el reemplazo ni el criterio de aceptación del GA.
    """
    same_design = (
        config.population_size == 100 and config.generations == 500
        and config.elitism == 2 and config.crossover_probability == 0.90
        and config.mutation_probability == 0.01 and seeds == list(range(30))
    )
    rows = []
    specs = [
        ("Corridas genéticas", "runs", 30, None),
        ("Evaluaciones genéticas", "total_evaluations", 1503000, None),
        ("Corridas aceptadas", "successes", 20, None),
        ("Éxito porcentual", "success_percent", 66.7, 1),
        ("Soluciones en P(0)", "initial_exact_individuals", 0, None),
        ("Primera llegada mínima", "first_zero_min", 3, None),
        ("Primera llegada máxima", "first_zero_max", 18, None),
        ("Mediana de primera llegada", "first_zero_median", 12, None),
        ("Diversidad inicial media", "initial_diversity_mean", 99.9, 1),
        ("Diversidad final media", "final_diversity_mean", 12.13, 2),
        ("J mínimo de fallos", "failed_J_min", 0.023440, 6),
        ("J máximo de fallos", "failed_J_max", 0.043224, 6),
    ]
    for label, key, published, decimals in specs:
        value = summary[key]
        shown = round(float(value), decimals) if decimals is not None and value is not None else value
        rows.append({
            "bloque": "Algoritmo genético", "indicador": label,
            "publicado": published, "calculado": value,
            "calculado_redondeado_comparable": shown,
            "coincide": shown == published if same_design else "No evaluado: parámetros distintos",
            "nota": "Mismos parámetros; orden de llamadas RNG explicitado en esta implementación."
                    if same_design else "Se ejecutó una configuración exploratoria diferente de V8.",
        })
    for row in bank["published_comparison"]:
        rows.append({
            "bloque": "Banco geométrico", "indicador": row["metric"],
            "publicado": row["published"], "calculado": row["observed"],
            "calculado_redondeado_comparable": row["observed"], "coincide": row["matches"],
            "nota": "Desglose de auxiliares definido explícitamente en el código."
                    if row["metric"] == "auxiliary_checks_passed" else "Conteo obtenido mediante enumeración exacta.",
        })
    return same_design, rows


def np_prepare_matplotlib(install_if_missing):
    """Comprueba la dependencia gráfica sin instalar programas por sorpresa.

    La opción de instalación, cuando se activa, utiliza el MISMO intérprete
    que está ejecutando el archivo. Esto evita instalar en otro Python de
    Anaconda. Un fallo no elimina las salidas numéricas ya calculadas.
    """
    if importlib.util.find_spec("matplotlib") is not None:
        return True
    if not install_if_missing:
        return False
    try:
        subprocess.run([sys.executable, "-m", "pip", "install", "matplotlib"], check=True)
        importlib.invalidate_caches()
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"No se pudo instalar Matplotlib: {exc}")
        return False
    return importlib.util.find_spec("matplotlib") is not None


def np_geometry_for_plot(geometry):
    """Convierte a decimal SOLO los datos que se enviarán a Matplotlib."""
    def pair(point):
        return float(point.x), float(point.y)
    return {
        "A": pair(geometry.triangle.a), "B": pair(geometry.triangle.b), "C": pair(geometry.triangle.c),
        "O": pair(geometry.O), "H": pair(geometry.H), "N": pair(geometry.N),
        "R2": float(geometry.R2), "r2": float(geometry.r2),
        "points": {label: pair(point) for label, point in geometry.points.items()},
    }


def np_write_readme(output_directory, metadata, summary, bank, encoding, comparisons, figures):
    """Informe de uso e interpretación construido a partir de la ejecución."""
    def show(value):
        if value is None:
            return "No aplica"
        if isinstance(value, Fraction):
            return f"{value} = {float(value):.12g}"
        return str(value)
    lines = [
        "CIRCUNFERENCIA DE LOS NUEVE PUNTOS", "Resultados calculados por el programa", "",
        f"Fecha local de ejecución: {metadata['started_at']}",
        f"Python utilizado: {metadata['python_version']}",
        f"SHA-256 del programa: {metadata['script_sha256']}", "",
        "LECTURA DEL PROGRAMA Y DEL ARTÍCULO", "",
        "Secciones 2.1 y 2.5: construct_geometry y verify_configuration calculan y verifican la geometría exacta.",
        "Secciones 2.2–2.4: GAFitnessModel y las funciones etapa_1...etapa_7 implementan la búsqueda.",
        "Sección 2.6: run_geometric_bank enumera la rejilla y ejecuta cuatro controles alterados.",
        "Sección 3.1: algebraic_trace explica y comprueba las igualdades (8)–(10) en el ejemplo.",
        "Secciones 3.2–3.3: se agregan corridas, se enumera la codificación y se estudian coincidencias de controles.",
        "Secciones 4–5: las métricas permiten interpretar convergencia, diversidad y límites del experimento.", "",
        "LAS SIETE ETAPAS", "",
        "1. Inicializar: 16 sorteos getrandbits(1) por individuo, desde el bit más significativo; se admiten duplicados.",
        "2. Evaluar: calcular tres residuos y su suma de cuadrados con enteros; convertir a Fraction solo para informar.",
        "3. Seleccionar: dos índices distintos por torneo mediante sample; choice resuelve todo empate.",
        "4. Cruzar: una decisión por pareja; corte uniforme entre 1 y 15 e intercambio de sufijos.",
        "5. Mutar: una decisión por bit de cada hijo; XOR invierte el bit cuando corresponde.",
        "6. Reemplazar: copias intactas de élites estables seguidas de todos los hijos, en orden.",
        "7. Terminar: consumir el presupuesto completo de generaciones y certificar el mejor candidato final.", "",
        "RESULTADOS DE ESTA EJECUCIÓN", "",
    ]
    labels = [
        ("Corridas", "runs"), ("Éxitos certificados", "successes"),
        ("Aproximaciones no certificadas", "failures"), ("Porcentaje de éxito", "success_percent"),
        ("Evaluaciones poblacionales", "total_evaluations"), ("Poblaciones registradas", "total_population_records"),
        ("Primera llegada mínima", "first_zero_min"), ("Primera llegada máxima", "first_zero_max"),
        ("Mediana entre corridas exitosas", "first_zero_median"),
        ("Diversidad inicial media", "initial_diversity_mean"), ("Diversidad final media", "final_diversity_mean"),
        ("J mínimo entre fallos", "failed_J_min"), ("J máximo entre fallos", "failed_J_max"),
    ]
    lines.extend(f"{label}: {show(summary[key])}" for label, key in labels)
    lines += ["", f"Centros con J=0 entre {encoding['codes_evaluated']} códigos: {encoding['zero_count']}",
              f"Ternas geométricas: {bank['total_triples']}; colineales: {bank['collinear_triples']}; válidas: {bank['valid_triangles']}",
              f"Residuos exactos nulos: {bank['zero_residuals']}",
              f"Denominadores de proyección positivos: {bank['positive_projection_denominators']}",
              f"Auxiliares satisfechas: {bank['auxiliary_checks_passed']}", "",
              "COMPARACIÓN CON EL ARTÍCULO", ""]
    lines.extend(f"{row['indicador']}: publicado={row['publicado']}; calculado={show(row['calculado'])}; coincide={row['coincide']}"
                 for row in comparisons)
    lines += ["", "ALCANCE DE LA REPRODUCCIÓN", "",
        "Los parámetros y semillas de V8 se conservan en la ejecución predeterminada. El artículo no publica todas las llamadas aleatorias ni su orden; aquí se documenta un protocolo completo. Una discrepancia en los agregados del GA no se oculta ni se corrige forzando datos. No se dispone del código original para reconstruir su traza exacta.",
        bank["auxiliary_description"],
        "La enumeración de la rejilla es una comprobación finita; no reemplaza la demostración del teorema. Las verificaciones auxiliares incluyen identidades dependientes. La frecuencia observada de éxito corresponde a este triángulo, esta codificación, estas semillas y este presupuesto.",
        "El centro matemático se utiliza para el certificado y los análisis; no se inserta en la población genética. El algoritmo no hace parada anticipada por J=0.", "",
        "ARCHIVOS GENERADOS", "",
        "tabla_1_nueve_puntos.csv: coordenadas, distancias y residuos calculados.",
        "tabla_2_candidatos.csv: cuatro ejemplos y sus errores recalculados.",
        "figura_3_operaciones.csv y ejemplos_operadores.json: cruce y mutación ilustrativos.",
        "tabla_3_controles.csv: definiciones explícitas de las cuatro alteraciones.",
        "tabla_4_banco.csv y tabla_5_controles.csv: conteos obtenidos por enumeración.",
        "corridas.csv: una fila por semilla, con candidato final, error y certificación.",
        "historial_generaciones.csv: métricas de todas las poblaciones, desde P(0) hasta P(G).",
        "poblaciones.csv.gz: cuando está activado, una fila por población; los 100 cromosomas se guardan en hexadecimal separados por espacios. int(texto,16) recupera cada código.",
        "traza_siete_etapas.json: primera transición REAL de la primera semilla, sin sorteos adicionales.",
        "rejilla_65536_centros.csv.gz: evaluación completa del espacio de códigos, independiente del GA.",
        "verificaciones_finales.json: nueve residuos y controles de construcción del mejor candidato de cada corrida.",
        "traza_algebraica.json: igualdades exactas asociadas con las ecuaciones (8)–(10).",
        "contraejemplo_euler.json: demuestra por qué comprobar distancias no basta para certificar construcciones.",
        "banco_geometrico.json: conteos completos, coincidencias individuales y nombres de las comprobaciones auxiliares.",
        "comparacion_articulo.csv: referencias publicadas junto a los valores realmente obtenidos.",
        "resumen_ejecucion.json: parámetros, versión, semilla, huella del código, métricas y observaciones.",
        "autocomprobaciones.json: pruebas de coherencia del programa, cuando están activadas.",
        f"Figuras generadas: {len(figures)} archivos. Los PNG son de 300 dpi y los SVG permiten ampliación vectorial.",
        "Los archivos .gz se abren con gzip.open en Python o con un descompresor compatible.", "",
        "DOCUMENTACIÓN DE LAS API", "https://docs.python.org/3.12/library/random.html",
        "https://docs.python.org/3.12/library/fractions.html",
        "https://matplotlib.org/stable/api/_as_gen/matplotlib.pyplot.savefig.html", "",
    ]
    (Path(output_directory) / "LEEME_resultados.txt").write_text("\n".join(lines), encoding="utf-8")


def np_output_directory(requested):
    """Crea una carpeta nueva y evita sobrescribir experimentos anteriores."""
    if requested:
        target = Path(requested).expanduser().resolve()
        if target.exists() and any(target.iterdir()):
            raise FileExistsError(f"La carpeta de salida ya contiene archivos: {target}. Elija otra con --salida.")
        target.mkdir(parents=True, exist_ok=True)
        return target
    base = Path(__file__).resolve().parent
    stem = "Resultados_Nueve_Puntos_" + datetime.now().strftime("%Y%m%d_%H%M%S")
    for index in range(1000):
        target = base / (stem if index == 0 else f"{stem}_{index:03d}")
        try:
            target.mkdir()
            return target
        except FileExistsError:
            continue
    raise OSError("No fue posible crear una carpeta nueva para los resultados.")


def np_argument_parser():
    """Opciones de terminal equivalentes a CONFIGURACION_USUARIO."""
    d = CONFIGURACION_USUARIO
    parser = argparse.ArgumentParser(description="Algoritmo genético de siete etapas y certificado exacto de los nueve puntos.")
    parser.add_argument("--poblacion", type=int, default=d["poblacion"])
    parser.add_argument("--generaciones", type=int, default=d["generaciones"])
    parser.add_argument("--corridas", type=int, default=d["corridas"])
    parser.add_argument("--semilla-inicial", type=int, default=d["primera_semilla"])
    parser.add_argument("--cruce", type=float, default=d["probabilidad_cruce"])
    parser.add_argument("--mutacion", type=float, default=d["probabilidad_mutacion"])
    parser.add_argument("--elites", type=int, default=d["elites"])
    parser.add_argument("--salida", help="Carpeta nueva o vacía para las salidas.")
    parser.add_argument("--sin-figuras", action="store_true", default=not d["generar_figuras"])
    parser.add_argument("--sin-poblaciones", action="store_true", default=not d["guardar_poblaciones_completas"])
    parser.add_argument("--sin-pruebas", action="store_true", default=not d["ejecutar_autocomprobaciones"])
    parser.add_argument("--solo-pruebas", action="store_true", help="Ejecuta autocomprobaciones sin el experimento completo.")
    parser.add_argument("--instalar-matplotlib", action="store_true", default=d["instalar_matplotlib_si_falta"])
    return parser


def main(argv=None):
    """Organiza la ejecución completa sin depender del documento Word original."""
    args = np_argument_parser().parse_args(argv)
    if args.corridas < 1:
        raise ValueError("El número de corridas debe ser positivo.")
    if args.semilla_inicial < 0:
        raise ValueError("La primera semilla debe ser un entero no negativo.")
    config = GAConfig(population_size=args.poblacion, generations=args.generaciones,
                      crossover_probability=args.cruce, mutation_probability=args.mutacion,
                      elitism=args.elites)
    seeds = list(range(args.semilla_inicial, args.semilla_inicial + args.corridas))
    started = time.perf_counter()
    started_at = datetime.now().astimezone().isoformat(timespec="seconds")
    print("Circunferencia de los nueve puntos — algoritmo genético de siete etapas")
    print(f"Python {platform.python_version()}; {len(seeds)} corridas; población {config.population_size}; generaciones {config.generations}.")

    geometry = construct_geometry(*VERTICES_ESTUDIO)
    model = GAFitnessModel.from_geometry_data([p.as_pair() for p in geometry.side_midpoints], geometry.R2)
    checks = {"performed": False}
    if not args.sin_pruebas or args.solo_pruebas:
        print("Verificando aritmética exacta y operadores...")
        checks = {"performed": True, "geometry": run_geometry_self_checks(include_bank=False),
                  "genetic_algorithm": ga_run_self_checks()}
        if args.solo_pruebas:
            print(json.dumps(np_json_ready(checks), ensure_ascii=False, indent=2))
            return 0
    out = np_output_directory(args.salida)
    print(f"Carpeta de resultados: {out}")
    np_save_json(out / "autocomprobaciones.json", checks)
    examples = np_manual_examples(model, config)
    np_save_csv(out / "tabla_1_nueve_puntos.csv", example_table_rows())
    np_save_csv(out / "tabla_2_candidatos.csv", examples["table2_rows"])
    np_save_csv(out / "figura_3_operaciones.csv", examples["figure3_rows"])
    np_save_json(out / "ejemplos_operadores.json", examples)
    np_save_json(out / "traza_algebraica.json", algebraic_trace(geometry))
    np_save_json(out / "contraejemplo_euler.json", euler_distance_counterexample())
    np_save_csv(out / "tabla_3_controles.csv", [
        {"control": "Centro desplazado", "alteracion": "N* = N + (1,0)", "posiciones_contadas": "Los nueve puntos"},
        {"control": "Radio incorrecto", "alteracion": "r*² = R²/3; residuo = 4d² - 4R²/3", "posiciones_contadas": "Los nueve puntos"},
        {"control": "Pies en tercios", "alteracion": "Da* = B + (C-B)/3; permutaciones cíclicas", "posiciones_contadas": "Da, Db, Dc; también se comprueban los otros seis"},
        {"control": "Euler en tercios", "alteracion": "Ea* = (2A+H)/3; permutaciones cíclicas", "posiciones_contadas": "Ea, Eb, Ec; también se comprueban los otros seis"},
    ])

    runs = []
    # Un contexto cierra el archivo comprimido incluso si el usuario interrumpe
    # la ejecución. Cada fila conserva TODA la población, incluidos duplicados.
    with ExitStack() as stack:
        sink = None
        if not args.sin_poblaciones:
            stream = stack.enter_context(gzip.open(out / "poblaciones.csv.gz", "wt", encoding="utf-8", newline="", compresslevel=6))
            writer = csv.writer(stream)
            writer.writerow(["semilla", "generacion", "cromosomas_hex_en_orden"])
            def sink(seed, generation, population):
                writer.writerow([seed, generation, " ".join(f"{code:04x}" for code in population)])
        for index, seed in enumerate(seeds):
            run = run_ga(seed, config, model,
                         verify_callback=lambda point: verify_configuration(geometry, center=point),
                         population_sink=sink, capture_first_transition=(index == 0))
            runs.append(run)
            status = "ACEPTADO" if run["accepted"] else "aproximación no certificada"
            print(f"  Semilla {seed:3d}: Q={tuple(str(x) for x in run['final_center'])}, J={float(run['best_J']):.10g}, {status}; primera llegada={run['first_zero_generation']}")

    summary = np_summarize_runs(runs)
    np_save_csv(out / "historial_generaciones.csv", ({"seed": run["seed"], **row} for run in runs for row in run["history"]))
    np_save_csv(out / "corridas.csv", [{
        "semilla": run["seed"], "codigo_hex": f"{run['final_code']:04x}",
        "cromosoma": np_chromosome_text(run["final_code"]),
        "qx_exacto": run["final_center"][0], "qy_exacto": run["final_center"][1],
        "K_entero": run["best_k"], "J_exacto": run["best_J"], "J_decimal": float(run["best_J"]),
        "aceptado": run["accepted"], "primera_generacion_cero": run["first_zero_generation"],
        "generaciones_completas": len(run["history"]) - 1, "evaluaciones": run["evaluations"],
        "diversidad_inicial": run["history"][0]["diversity"], "diversidad_final": run["history"][-1]["diversity"],
    } for run in runs])
    np_save_json(out / "traza_siete_etapas.json", runs[0]["first_transition"])
    np_save_json(out / "verificaciones_finales.json", [{"seed": run["seed"], "candidate": run["final_center"], "verification": run["verification"]} for run in runs])

    print("Enumerando los 65,536 centros representables...")
    encoding, fitness_grid = np_enumerate_encoding(model, out)
    np_save_json(out / "enumeracion_codificacion.json", encoding)
    print("Enumerando la rejilla geométrica y los cuatro controles exactos...")
    bank = run_geometric_bank(include_details=False)
    np_save_csv(out / "tabla_4_banco.csv", bank["table4_rows"])
    np_save_csv(out / "tabla_5_controles.csv", bank["table5_rows"])
    np_save_json(out / "banco_geometrico.json", bank)
    same_design, comparisons = np_compare_article(summary, bank, config, seeds)
    np_save_csv(out / "comparacion_articulo.csv", comparisons)

    figures = []
    graphic_observation = "Figuras desactivadas por configuración."
    if not args.sin_figuras:
        if np_prepare_matplotlib(args.instalar_matplotlib):
            print("Generando las figuras a partir de los resultados calculados...")
            try:
                figures = generate_figures(out, np_geometry_for_plot(geometry), runs, examples, fitness_grid)
                graphic_observation = f"Se generaron {len(figures)} archivos gráficos."
            except ImportError as exc:
                graphic_observation = str(exc)
                print("No se pudieron generar las figuras: " + graphic_observation)
        else:
            graphic_observation = "Matplotlib no está disponible. Los resultados numéricos están completos; para obtener figuras, instale matplotlib y ejecute de nuevo."
            print(graphic_observation)
    source = Path(__file__).resolve()
    metadata = {
        "source_article": "ARTICULO-01-NUEVE-PUNTOS-V8.docx",
        "started_at": started_at, "elapsed_seconds": time.perf_counter() - started,
        "python_version": platform.python_version(), "python_implementation": platform.python_implementation(),
        "matplotlib_version": getattr(sys.modules.get("matplotlib"), "__version__", None),
        "platform": platform.platform(), "script_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "configuration": asdict(config), "seeds": seeds, "same_parameters_as_article": same_design,
        "random_protocol": "Random(seed) una vez; getrandbits(1) MSB; todos los torneos con sample y choice; todos los cruces con random/randrange; todas las mutaciones con random de MSB a LSB; elitismo estable sin reordenar la población de torneos.",
        "numeric_policy": "Comparación genética con K entero; certificados con Fraction; floats solo para presentación y probabilidades de operadores.",
        "graphical_observation": graphic_observation,
        "full_populations_saved": not args.sin_poblaciones,
        "limits": [
            "No se dispone de la traza ni del código fuente original; los agregados estocásticos pueden diferir.",
            "Las 21 auxiliares tienen un desglose explícito de esta implementación, no enumerado en V8.",
            "El banco finito no constituye por sí solo una demostración universal ni verificación formal del software.",
        ],
    }
    np_save_json(out / "resumen_ejecucion.json", {"metadata": metadata, "genetic_results": summary, "encoding": encoding, "geometric_counts": {key: bank[key] for key in ("total_triples", "collinear_triples", "valid_triangles", "residuals_calculated", "zero_residuals", "positive_projection_denominators", "auxiliary_checks_passed")}, "figures": [Path(path).name for path in figures]})
    np_write_readme(out, metadata, summary, bank, encoding, comparisons, figures)
    print(f"\nFinalizado: {summary['successes']}/{summary['runs']} corridas certificadas ({summary['success_percent']:.2f}%).")
    print(f"Evaluaciones genéticas: {summary['total_evaluations']:,}; triángulos válidos: {bank['valid_triangles']:,}; residuos nulos: {bank['zero_residuals']:,}.")
    print("Consulte LEEME_resultados.txt y comparacion_articulo.csv para interpretar la ejecución.")
    print(f"Resultados: {out}")
    return 0


if __name__ == "__main__":
    # En Spyder, F5 ejecuta este bloque; importar el archivo como módulo permite
    # utilizar sus funciones sin lanzar automáticamente las 30 corridas.
    try:
        exit_status = main()
    except KeyboardInterrupt:
        print("\nEjecución interrumpida; la carpeta creada puede contener resultados parciales.", file=sys.stderr)
        exit_status = 130
    except (ValueError, TypeError, OSError, AssertionError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        exit_status = 1
    if exit_status:
        raise SystemExit(exit_status)
