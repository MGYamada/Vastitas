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
    pub source: Vec<AssemblyItem>,
    pub events: Vec<EditEvent>,
    pub span: Span,
    #[serde(skip)]
    pub expanded_count: usize,
}

/// A flat sequence of source items keeps lexical nesting independent of JSON depth.
/// The checker reconstructs implicit loan names, returns and seals from these items.
#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum AssemblyItem {
    Family {
        target: Vec<String>,
        span: Span,
    },
    Borrow {
        grant: Vec<String>,
        label: Option<String>,
        span: Span,
    },
    Delegate {
        delegation: Vec<String>,
        label: Option<String>,
        span: Span,
    },
    Apply {
        contributions: Vec<Vec<String>>,
        span: Span,
    },
    Transfer {
        declaration: Vec<String>,
        span: Span,
    },
    Close {
        span: Span,
    },
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
    /// may not (`packages::prepare_function_families`). Not part of the request.
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

impl Module {
    /// Every source reference that can select an existing function for editing.
    /// An unqualified method with no local header can itself be an import alias.
    pub(crate) fn edit_targets(&self) -> impl Iterator<Item = Vec<String>> + '_ {
        self.grants
            .iter()
            .map(|d| &d.declaration.target)
            .chain(self.delegations.iter().map(|d| &d.declaration.target))
            .chain(self.transfers.iter().map(|d| &d.declaration.target))
            .chain(self.contributions.iter().map(|d| &d.declaration.target))
            .cloned()
            .chain(
                self.methods
                    .iter()
                    .map(|m| m.name.split("::").map(str::to_owned).collect()),
            )
            .chain(
                self.abstract_methods
                    .iter()
                    .map(|c| c.name.split("::").map(str::to_owned).collect()),
            )
    }
}

pub(crate) struct Parsed {
    pub modules: Vec<Module>,
    pub external: Vec<External>,
}
