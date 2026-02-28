#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

"""
Pydantic Model Introspection Script

Extracts type information from Pydantic models and outputs JSON
that can be parsed by the protocol-squisher Rust analyzer.

Usage:
    python introspect_pydantic.py <module_path> [model_names...]

Examples:
    python introspect_pydantic.py myapp.models
    python introspect_pydantic.py myapp.models User Order
"""

import sys
import json
import importlib
import inspect
from typing import Any, Dict, List, Optional, Union, get_origin, get_args
from types import NoneType
from enum import Enum
from datetime import datetime, date, time, timedelta
from decimal import Decimal
from uuid import UUID

# Pydantic v2 imports
try:
    from pydantic import BaseModel
    from pydantic.fields import FieldInfo
    from pydantic_core import PydanticUndefined
    PYDANTIC_V2 = True
except ImportError:
    # Pydantic v1 fallback
    try:
        from pydantic import BaseModel
        from pydantic.fields import FieldInfo, Undefined as PydanticUndefined
        PYDANTIC_V2 = False
    except ImportError:
        print(json.dumps({"error": "Pydantic not installed"}))
        sys.exit(1)


def get_type_name(tp: Any) -> Dict[str, Any]:
    """Convert a Python type annotation to a serializable representation."""

    # Handle None/NoneType
    if tp is None or tp is NoneType:
        return {"kind": "none"}

    # Handle basic types
    if tp is str:
        return {"kind": "primitive", "type": "string"}
    if tp is int:
        return {"kind": "primitive", "type": "int"}
    if tp is float:
        return {"kind": "primitive", "type": "float"}
    if tp is bool:
        return {"kind": "primitive", "type": "bool"}
    if tp is bytes:
        return {"kind": "primitive", "type": "bytes"}

    # Handle common types
    if tp is datetime:
        return {"kind": "primitive", "type": "datetime"}
    if tp is date:
        return {"kind": "primitive", "type": "date"}
    if tp is time:
        return {"kind": "primitive", "type": "time"}
    if tp is timedelta:
        return {"kind": "primitive", "type": "duration"}
    if tp is Decimal:
        return {"kind": "primitive", "type": "decimal"}
    if tp is UUID:
        return {"kind": "primitive", "type": "uuid"}

    # Handle Any
    if tp is Any:
        return {"kind": "any"}

    # Get origin for generic types
    origin = get_origin(tp)
    args = get_args(tp)

    # Handle Optional (Union with None)
    if origin is Union:
        non_none_args = [a for a in args if a is not NoneType]
        if len(non_none_args) == 1 and NoneType in args:
            # This is Optional[T]
            return {
                "kind": "optional",
                "inner": get_type_name(non_none_args[0])
            }
        # This is a real Union
        return {
            "kind": "union",
            "variants": [get_type_name(a) for a in args]
        }

    # Handle List/list
    if origin is list:
        inner = args[0] if args else Any
        return {
            "kind": "list",
            "inner": get_type_name(inner)
        }

    # Handle Set/set
    if origin is set or origin is frozenset:
        inner = args[0] if args else Any
        return {
            "kind": "set",
            "inner": get_type_name(inner)
        }

    # Handle Dict/dict
    if origin is dict:
        key = args[0] if len(args) > 0 else Any
        value = args[1] if len(args) > 1 else Any
        return {
            "kind": "map",
            "key": get_type_name(key),
            "value": get_type_name(value)
        }

    # Handle Tuple
    if origin is tuple:
        if args:
            return {
                "kind": "tuple",
                "elements": [get_type_name(a) for a in args]
            }
        return {"kind": "tuple", "elements": []}

    # Handle Enum classes
    if inspect.isclass(tp) and issubclass(tp, Enum):
        return {
            "kind": "enum",
            "name": tp.__name__,
            "module": tp.__module__,
            "variants": [{"name": m.name, "value": m.value} for m in tp]
        }

    # Handle Pydantic models (nested)
    if inspect.isclass(tp) and issubclass(tp, BaseModel):
        return {
            "kind": "reference",
            "name": tp.__name__,
            "module": tp.__module__
        }

    # Handle other classes
    if inspect.isclass(tp):
        return {
            "kind": "reference",
            "name": tp.__name__,
            "module": getattr(tp, "__module__", "unknown")
        }

    # Fallback for string annotations or unknown types
    if isinstance(tp, str):
        return {"kind": "reference", "name": tp}

    return {"kind": "unknown", "repr": repr(tp)}


def extract_field_constraints(field_info: FieldInfo) -> Dict[str, Any]:
    """Extract constraints from a Pydantic FieldInfo."""
    constraints = {}

    if PYDANTIC_V2:
        # Pydantic v2 metadata
        for meta in getattr(field_info, "metadata", []):
            meta_type = type(meta).__name__
            if hasattr(meta, "gt"):
                constraints["gt"] = meta.gt
            if hasattr(meta, "ge"):
                constraints["ge"] = meta.ge
            if hasattr(meta, "lt"):
                constraints["lt"] = meta.lt
            if hasattr(meta, "le"):
                constraints["le"] = meta.le
            if hasattr(meta, "multiple_of"):
                constraints["multiple_of"] = meta.multiple_of
            if hasattr(meta, "min_length"):
                constraints["min_length"] = meta.min_length
            if hasattr(meta, "max_length"):
                constraints["max_length"] = meta.max_length
            if hasattr(meta, "pattern"):
                constraints["pattern"] = meta.pattern
    else:
        # Pydantic v1
        if hasattr(field_info, "gt") and field_info.gt is not None:
            constraints["gt"] = field_info.gt
        if hasattr(field_info, "ge") and field_info.ge is not None:
            constraints["ge"] = field_info.ge
        if hasattr(field_info, "lt") and field_info.lt is not None:
            constraints["lt"] = field_info.lt
        if hasattr(field_info, "le") and field_info.le is not None:
            constraints["le"] = field_info.le
        if hasattr(field_info, "multiple_of") and field_info.multiple_of is not None:
            constraints["multiple_of"] = field_info.multiple_of
        if hasattr(field_info, "min_length") and field_info.min_length is not None:
            constraints["min_length"] = field_info.min_length
        if hasattr(field_info, "max_length") and field_info.max_length is not None:
            constraints["max_length"] = field_info.max_length
        if hasattr(field_info, "regex") and field_info.regex is not None:
            constraints["pattern"] = field_info.regex

    return constraints


def extract_model(model: type) -> Dict[str, Any]:
    """Extract type information from a Pydantic model."""

    fields = []

    if PYDANTIC_V2:
        # Pydantic v2
        model_fields = model.model_fields
        for name, field_info in model_fields.items():
            field_type = field_info.annotation

            # Check if field is optional
            is_optional = False
            if field_info.default is not PydanticUndefined:
                is_optional = True
            if field_info.default_factory is not None:
                is_optional = True

            # Get default value
            default = None
            if field_info.default is not PydanticUndefined:
                default = field_info.default
                # Try to serialize
                try:
                    json.dumps(default)
                except (TypeError, ValueError):
                    default = repr(default)

            fields.append({
                "name": name,
                "type": get_type_name(field_type),
                "optional": is_optional,
                "default": default,
                "alias": field_info.alias,
                "title": field_info.title,
                "description": field_info.description,
                "constraints": extract_field_constraints(field_info),
            })
    else:
        # Pydantic v1
        for name, field in model.__fields__.items():
            field_type = field.outer_type_

            is_optional = not field.required

            default = None
            if field.default is not PydanticUndefined:
                default = field.default
                try:
                    json.dumps(default)
                except (TypeError, ValueError):
                    default = repr(default)

            fields.append({
                "name": name,
                "type": get_type_name(field_type),
                "optional": is_optional,
                "default": default,
                "alias": field.alias if field.alias != name else None,
                "title": field.field_info.title,
                "description": field.field_info.description,
                "constraints": extract_field_constraints(field.field_info),
            })

    # Get model config
    config = {}
    if PYDANTIC_V2:
        model_config = getattr(model, "model_config", {})
        if model_config:
            config = dict(model_config)
    else:
        if hasattr(model, "Config"):
            cfg = model.Config
            for attr in ["extra", "frozen", "validate_assignment", "use_enum_values"]:
                if hasattr(cfg, attr):
                    val = getattr(cfg, attr)
                    if val is not None:
                        config[attr] = val

    return {
        "kind": "model",
        "name": model.__name__,
        "module": model.__module__,
        "doc": model.__doc__,
        "fields": fields,
        "config": config,
    }


def extract_enum(enum_class: type) -> Dict[str, Any]:
    """Extract type information from an Enum class."""
    return {
        "kind": "enum",
        "name": enum_class.__name__,
        "module": enum_class.__module__,
        "doc": enum_class.__doc__,
        "variants": [
            {"name": member.name, "value": member.value}
            for member in enum_class
        ]
    }


def find_models_in_module(module) -> List[type]:
    """Find all Pydantic BaseModel subclasses in a module."""
    models = []
    for name in dir(module):
        obj = getattr(module, name)
        if (inspect.isclass(obj)
            and issubclass(obj, BaseModel)
            and obj is not BaseModel
            and obj.__module__ == module.__name__):
            models.append(obj)
    return models


def find_enums_in_module(module) -> List[type]:
    """Find all Enum subclasses in a module."""
    enums = []
    for name in dir(module):
        obj = getattr(module, name)
        if (inspect.isclass(obj)
            and issubclass(obj, Enum)
            and obj is not Enum
            and obj.__module__ == module.__name__):
            enums.append(obj)
    return enums


def introspect_module(module_path: str, model_names: Optional[List[str]] = None) -> Dict[str, Any]:
    """Introspect a Python module and extract Pydantic model definitions."""

    try:
        module = importlib.import_module(module_path)
    except ImportError as e:
        return {"error": f"Failed to import module: {e}"}

    result = {
        "module": module_path,
        "pydantic_version": 2 if PYDANTIC_V2 else 1,
        "types": [],
    }

    # Find all models
    all_models = find_models_in_module(module)
    all_enums = find_enums_in_module(module)

    # Filter by name if specified
    if model_names:
        all_models = [m for m in all_models if m.__name__ in model_names]
        all_enums = [e for e in all_enums if e.__name__ in model_names]

    # Extract models
    for model in all_models:
        try:
            result["types"].append(extract_model(model))
        except Exception as e:
            result["types"].append({
                "kind": "error",
                "name": model.__name__,
                "error": str(e)
            })

    # Extract enums
    for enum_class in all_enums:
        try:
            result["types"].append(extract_enum(enum_class))
        except Exception as e:
            result["types"].append({
                "kind": "error",
                "name": enum_class.__name__,
                "error": str(e)
            })

    return result


def main():
    if len(sys.argv) < 2:
        print(json.dumps({
            "error": "Usage: introspect_pydantic.py <module_path> [model_names...]"
        }))
        sys.exit(1)

    module_path = sys.argv[1]
    model_names = sys.argv[2:] if len(sys.argv) > 2 else None

    result = introspect_module(module_path, model_names)
    print(json.dumps(result, indent=2, default=str))


if __name__ == "__main__":
    main()
