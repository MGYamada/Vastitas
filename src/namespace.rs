//! The package-mode records of a request: the modules of a package with
//! their imports, visibility and edit-authority declarations. The parser
//! writes them, and `packages::load` gathers them into the request. Their
//! namespace references stay unresolved; the kernel resolves them.
use crate::ir::{AbstractMethod, AbstractType, Function, Generic, Method, Span, Subtype};
use serde::Serialize;

#[derive(Debug, Serialize)]
pub(crate) struct Grant {
    pub name: String,
    pub target: Vec<String>,
    pub grantee_package: String,
    pub grantee_path: Vec<String>,
    pub region: Vec<Vec<String>>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub delegable: bool,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Transfer {
    pub name: String,
    pub target: Vec<String>,
    pub grantee_package: String,
    pub grantee_path: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Contribution {
    pub name: String,
    pub target: Vec<String>,
    pub methods: Vec<Method>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Assembly {
    pub events: Vec<EditEvent>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub(crate) enum EditEvent {
    Borrow {
        grant: Vec<String>,
        loan: String,
        span: Span,
    },
    Apply {
        contribution: Vec<String>,
        loan: Option<String>,
        span: Span,
    },
    Return {
        loan: String,
        span: Span,
    },
    Seal {
        target: Vec<String>,
        span: Span,
    },
    Reborrow {
        parent: String,
        delegation: Vec<String>,
        loan: String,
        span: Span,
    },
    Transfer {
        declaration: Vec<String>,
        span: Span,
    },
}

#[derive(Debug, Serialize)]
pub(crate) struct Public<T> {
    #[serde(flatten)]
    pub declaration: T,
    pub public: bool,
}

#[derive(Debug, Serialize)]
pub(crate) struct Import {
    pub path: Vec<String>,
    pub alias: String,
    pub public: bool,
    pub span: Span,
    /// The place of the name that a `use` without `as` binds, when that name
    /// is a compatibility spelling: the parser cannot tell whether the path
    /// names an `indexed` declaration, which may take it, or a module, which
    /// may not (`reserved_module_uses`). Not part of the request.
    #[serde(skip)]
    pub deferred_name: Option<Span>,
}

#[derive(Debug, Serialize)]
pub(crate) struct Module {
    pub path: Vec<String>,
    pub public: bool,
    pub imports: Vec<Import>,
    pub functions: Vec<Public<Function>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub resource_functions: Vec<Public<crate::storage::source::Function>>,
    pub generics: Vec<Public<Generic>>,
    pub methods: Vec<Method>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub indexed_declarations: Vec<Public<crate::indexed::Declaration>>,
    #[serde(skip)]
    pub uses_indexed: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub abstract_types: Vec<Public<AbstractType>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub subtypes: Vec<Subtype>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub abstract_methods: Vec<AbstractMethod>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub grants: Vec<Public<Grant>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegations: Vec<Public<Grant>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub transfers: Vec<Public<Transfer>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub contributions: Vec<Public<Contribution>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assembly: Option<Assembly>,
    pub span: Span,
}

pub(crate) struct External {
    pub path: Vec<String>,
    pub public: bool,
    pub span: Span,
}

pub(crate) struct Parsed {
    pub modules: Vec<Module>,
    pub external: Vec<External>,
}
